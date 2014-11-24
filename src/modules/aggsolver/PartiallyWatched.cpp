/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#include "modules/aggsolver/PartiallyWatched.hpp"

#include "modules/aggsolver/AggPrint.hpp"
#include "modules/aggsolver/AggSet.hpp"
#include "theorysolvers/PCSolver.hpp"
#include "utils/NumericLimits.hpp"
#include "external/utils/ContainerUtils.hpp"

#include <cstdint>
#include <cinttypes>
#include <climits>
#include <set>

using namespace std;
using namespace MinisatID;

/**
 * TODO sorted aggr?
 * TODO maximum aggregate?
 *
 * Note: only works for sum and prod aggregates with positive weights!
 */

GenPWAgg::GenPWAgg(TypedSet* set)
		: AggPropagator(set), emptyinterpretbounds(Weight(0), Weight(0)), certainlyreconstruct(false) {
}

GenPWAgg::~GenPWAgg() {
//	deleteList<GenPWatch>(ws);
//	deleteList<GenPWatch>(nws);
}

/**
 * @pre All aggregates have the same sign and HEAD OR AGG instead of equivalence, so the head can be negative!
 * initialize NWS: make a watch for each set literal, watch the negation of the set literal if its monotone
 *					then reconstruct the set for the aggregate with the lowest bound!
 */
void GenPWAgg::internalInitialize(bool& unsat, bool& sat) {
#ifdef DEBUG
	MAssert(getAgg().size()>0);
	AggSign sign = getAgg()[0]->getSign();
	for(auto i=getAgg().cbegin(); i<getAgg().cend(); ++i) {
		MAssert((*i)->getSign()==sign);
		MAssert((*i)->getSem()==AggSem::OR);
	}
#endif

	auto& set = getSet();
	auto wls = set.getWL();

	// TODO duplicate with fully watched
#ifdef NOARBITPREC
	if (getType().getType() == AggType::PROD) {
		//Test whether the total product of the weights is not infinity for intweights
		Weight total(1);
		for (auto i = getSet().getWL().cbegin(); i < getSet().getWL().cend(); ++i) {
			if (posInfinity() / total < i->getWeight()) {
				throw idpexception("The total product of weights exceeds max-int, correctness cannot be guaranteed in limited precision.\n");
			}
			total *= i->getWeight();
		}
	}
#endif

	makeSumSetPositive(getSet());

	setBoundsOnEmptyInterpr(minmaxBounds(getType().getMinPossible(set), getType().getMaxPossible(set)));

	// Create watches (they are sorted small to large, and nws is initially sorted inverse!)
	for (auto i = wls.rbegin(); i < wls.rend(); ++i) {
		auto mono = getType().isMonotone(**getAgg().cbegin(), i->getWeight());
		nws.push_back(new GenPWatch(getSetp(), *i, mono, nws.size()));
	}

	// FIXME for reverse trail, only use rootValues here?

	// Check initial derivations
	checkInitiallyKnownAggs(unsat, sat);
	if (unsat || sat) {
		return;
	}

	// Calculate reference aggregate (the one which will lead to the most watches)
	worstagg = getAggWithMostStringentBound(true);
	MAssert(worstagg != NULL);

	// Construct first watches
	bool propagations = false;
	auto confl = reconstructSet(propagations, NULL);
	if (confl != nullPtrClause) {
		unsat = true;
		return;
	}
	addStagedWatchesToNetworkOnStable(confl);
}

rClause GenPWAgg::reInitialize() {
	worstagg = getAggWithMostStringentBound(true);
	MAssert(worstagg != NULL);
	// FIXME can this happen?

	bool propagations = false;
	auto confl = reconstructSet(propagations, NULL);
	//if (confl == nullPtrClause) {
	//	confl = propagateAtEndOfQueue(); // TODO why necessary here and not in initialize?
	//}
	addStagedWatchesToNetworkOnStable(confl);
	//notifyFirstPropagation(mkPosLit(-1));
	return confl;
}

void GenPWAgg::propagate(int, Watch* ws, int) {
	proplist.push_back(ws);
}
void GenPWAgg::propagate(const Lit&, Watch* ws, int) {
	proplist.push_back(ws);
}

void GenPWAgg::backtrack(int untillevel) {
	bool needreconstruction = false;
	while (backtracklist.size() > 0 && backtracklist.back().second > untillevel) {
		needreconstruction = true;
		backtracklist.pop_back();
	}
	if (needreconstruction) {
		proplist.clear();
		certainlyreconstruct = true;
		getSet().getPCSolver().acceptForPropagation(getSetp());
	}
}

rClause GenPWAgg::propagateAtEndOfQueue() {
	auto confl = nullPtrClause;
	std::vector<GenPWatch*> watchlist;
	auto propagations = false;
	auto somesetwatch = false;
	for (uint i = 0; confl == nullPtrClause && i < proplist.size(); ++i) {
		auto watch = proplist[i];
		if (watch->headWatch()) { // Can only happen once
			MAssert(not watch->dynamic());
			confl = reconstructSet(propagations, getAgg()[watch->getAggIndex()]);
		} else {
			auto gw = dynamic_cast<GenPWatch*>(watch);
			MAssert(watch!=NULL);
			if (value(gw->getPropLit()) != l_True) { // NOTE: it is possible that we already backtracked over some fired watch
				continue;
			}
			watchlist.push_back(gw);
			if (not gw->isInWS()) { //Already in NWS, so no need to watch it
				MAssert(getNWS()[gw->getIndex()]==watch);
				//Check it really is in NWS
			} else {
				somesetwatch = true;
			}
		}
	}
	if (confl == nullPtrClause && (somesetwatch || certainlyreconstruct)) {
		confl = reconstructSet(propagations, NULL);
	}
	for (auto i = watchlist.cbegin(); somesetwatch && i < watchlist.cend(); ++i) {
		MAssert(value((*i)->getPropLit()) == l_True);
		// FIXME this condition is VERY ad-hoc and should move inside
		if (watchlist.size() == 1 && not certainlyreconstruct && not propagations && confl == nullPtrClause) { //It can be safely removed as a watch
			moveFromWSToNWS(*i);
		} else { //Otherwise, add it again to the network
			if (not (*i)->isInNetwork()) {
				getSet().getPCSolver().accept(*i);
			}
		}
	}

	for (auto i = getWS().cbegin(); i < getWS().cend(); ++i) {
		if (getPCSolver().value((*i)->getPropLit()) == l_Undef) {
			stageWatch(*i);
		}
	}

	certainlyreconstruct = false;
	addStagedWatchesToNetworkOnStable(confl);
	proplist.clear();

	if (getSet().verbosity() > 9) {
		clog << "Backtracklist for set " << getSet().getSetID() << " : ";
		for (auto i = backtracklist.cbegin(); i < backtracklist.cend(); ++i) {
			clog << "level " << i->second << " -> var " << toString(i->first, getPCSolver()) << ", ";
		}
		clog << "\n";
	}

	return confl;
}

void GenPWAgg::checkInitiallyKnownAggs(bool& unsat, bool& sat) {
	auto pessbounds = calculatePessimisticBounds();

	auto confl = nullPtrClause;
	std::set<Agg*> del;
	for (auto i = getAgg().cbegin(); confl == nullPtrClause && i < getAgg().cend(); ++i) {
		if ((*i)->isOptim()) {
			continue;
		}
		if (value((*i)->getHead()) == l_True) { //Head always true
			del.insert(*i);
		} else if (isSatisfied(**i, pessbounds)) { // Agg always true
			del.insert(*i);
		} else if (isFalsified(**i, pessbounds)) { // Agg always false, so head has to be true
			confl = getSet().notifySolver(new HeadReason(**i, (*i)->getHead()));
			del.insert(*i);
		}
	}
	getSet().removeAggs(del);
	if (confl != nullPtrClause) {
		unsat = true;
	} else if (getAgg().size() == 0) {
		sat = true;
	}
}

minmaxBounds GenPWAgg::calculatePessimisticBounds() {
	auto pessbounds = getBoundsOnEmptyInterpr();
	for (auto i = getSet().getWL().cbegin(); i < getSet().getWL().cend(); ++i) {
		auto wl = *i;
		lbool val = value(wl.getLit());
		if (val == l_True) {
			pessbounds.min = getType().add(pessbounds.min, wl.getWeight());
		} else if (val == l_False) {
			pessbounds.max = getType().removeMax(pessbounds.max, wl.getWeight());
		}
	}
	return pessbounds;
}

// Can return NULL, if no heads are false (or unknown if includeunknown)
Agg* GenPWAgg::getAggWithMostStringentBound(bool includeunknown) const {
	Agg* strongestagg = NULL;
	for (auto i = getAgg().cbegin(); i < getAgg().cend(); ++i) {
		bool relevantagg = false; // NOTE: recall HEAD OR AGG
		if (includeunknown) {
			relevantagg |= value((*i)->getHead()) != l_True;
		} else {
			relevantagg |= value((*i)->getHead()) == l_False;
		}
		if (relevantagg) {
			if (strongestagg == NULL) {
				strongestagg = *i;
			} else if (strongestagg->hasLB() && strongestagg->getBound() < (*i)->getBound()) {
				strongestagg = *i;
			} else if (strongestagg->hasUB() && strongestagg->getBound() > (*i)->getBound()) {
				strongestagg = *i;
			}
		}
	}
	return strongestagg;
}

void GenPWAgg::stageWatch(GenPWatch* watch) {
	getStagedWatches().push_back(watch);
}

const agglist& GenPWAgg::getAgg() const {
	return getSet().getAgg();
}

const AggProp& GenPWAgg::getType() const {
	return getSet().getType();
}

void GenPWAgg::moveFromTo(GenPWatch* watch, genwatchlist& from, genwatchlist& to) {
	if (from.size() > 1) {
		uint index = watch->getIndex();
		from[index] = from[from.size() - 1];
		from[index]->setIndex(index);
	}
	from.pop_back();

	to.push_back(watch);
	watch->setIndex(to.size() - 1);
	watch->movedToOther();

#ifdef DEBUG
	MAssert(getNWS().size()+getWS().size()==getSet().getWL().size());
#endif
}

void GenPWAgg::moveFromNWSToWS(GenPWatch* watch) {
	moveFromTo(watch, getNWS(), getWS());
}

void GenPWAgg::moveFromWSToNWS(GenPWatch* watch) {
	moveFromTo(watch, getWS(), getNWS());
}

void GenPWAgg::addWatchToNetwork(GenPWatch* watch) {
	MAssert(watch->isInWS());
	if (not watch->isInNetwork() && getPCSolver().value(watch->getPropLit()) == l_Undef) {
		getSet().getPCSolver().accept(watch);
	}
}

void GenPWAgg::resetStagedWatches(int startindex) {
	getStagedWatches().erase(getStagedWatches().begin() + startindex, getStagedWatches().end());
}

void GenPWAgg::addStagedWatchesToNetworkOnStable(rClause confl) {
	if (confl != nullPtrClause) {
		resetStagedWatches();
		return;
	}
	for (auto i = getStagedWatches().cbegin(); i < getStagedWatches().cend(); ++i) {
		if (not (*i)->isInWS()) {
			moveFromNWSToWS(*i);
		}
		if (not (*i)->isInNetwork()) {
			addWatchToNetwork(*i);
		}
	}
	getStagedWatches().clear();
	if (getPCSolver().verbosity() > 5) {
		clog << "Watches of \n\t";
		print(getPCSolver().verbosity(), getSet(), true);
		clog << "\twith aggregates \n";
		for (auto i = getAgg().cbegin(); i < getAgg().cend(); ++i) {
			clog << "\t\t";
			print(getPCSolver().verbosity(), **i, true);
		}
		clog << "\t are ";
		for (auto i = getWS().cbegin(); i < getWS().cend(); ++i) {
			if ((*i)->isInNetwork()) {
				clog << toString((*i)->getWatchLit(), getPCSolver()) << " ";
			} else {
				clog << "(" << toString((*i)->getWatchLit(), getPCSolver()) << ") "; // Not in network!
			}

		}
		clog << "\n";
	}
}

/**
 * do propagation, both body and heads:
 * 		calc full min and max
 * reconstruct watches:
 * 		calc min and max of watched set and store largest non-false weight
 * 		keep adding non-false until satisfied
 * 		if head known
 * 			remove largest, keep adding non-false until satisfied
 *  FIXME propagations is wrong name (instead means "keep watch"?)
 */
rClause GenPWAgg::reconstructSet(bool& propagations, Agg const * propagg) {
//#ifdef DEBUG
//	checkWatches();
//#endif
	MAssert(backtracklist.size()==0 || backtracklist.back().second<=getPCSolver().getCurrentDecisionLevel());

	auto confl = nullPtrClause;
	auto oneagg = getAgg().size() == 1;

	//possible HACK: always keep watch
	//propagations = true;

	if (oneagg && value((*getAgg().cbegin())->getHead()) == l_True) { // NOTE: recall head OR agg
		return confl;
	}

	uint nwsindex = 0;
	GenPWatch* largestunkn = NULL;
	const auto& worstagg = *getWorstAgg();
	auto bounds = calculateBoundsOfWatches(largestunkn);

	genWatches(nwsindex, worstagg, bounds, largestunkn);

	if (not isSatisfied(worstagg, bounds.optim)) {
		// can certainly propagate head
		confl = checkPropagation(propagations, bounds.pess, propagg);
	} else if (oneagg && value((*getAgg().cbegin())->getHead()) == l_Undef) {
		// if head is still unknown, one ws suffices
	} else if (largestunkn == NULL || isSatisfied(worstagg, bounds.pess)) {
		// certainly satisfied
		notifyFirstPropagation(mkPosLit(getMaxElem<int>()));
		propagations = true;
	} else {
		uint storednwsindex = nwsindex, storedstagedindex = getStagedWatches().size();
		auto storedbounds = bounds;

		//Leave out largest
		MAssert(largestunkn!=NULL);
		removeValue(getType(), largestunkn->getWL().getWeight(), largestunkn->isMonotone(), bounds.optim);

		auto templargest = largestunkn;
		genWatches(nwsindex, worstagg, bounds, templargest);

		if (not isSatisfied(worstagg, bounds.optim)) {
			confl = checkPropagation(propagations, bounds.pess, propagg);

			if (confl != nullPtrClause) {
				propagations = true;
			} else {
				//TODO can it be done cheaper?
				resetStagedWatches(storedstagedindex);
				bounds = storedbounds;
				nwsindex = storednwsindex;
				genWatches(nwsindex, worstagg, bounds, largestunkn);
			}
		}
	}

//#ifdef DEBUG
//	checkWatches();
//#endif

	return confl;
}

void GenPWAgg::checkWatches() const {
	for (auto i = getSet().getWL().cbegin(); i < getSet().getWL().cend(); ++i) {
#ifndef NDEBUG
		bool found = false;
#endif
		for (auto j = getNWS().cbegin(); j < getNWS().cend(); ++j) {
			if (var(i->getLit()) == var((*j)->getWL().getLit())) {
#ifndef NDEBUG
				found = true;
#endif
			}
		}
		for (auto j = getWS().cbegin(); j < getWS().cend(); ++j) {
			if (var(i->getLit()) == var((*j)->getWL().getLit())) {
#ifndef NDEBUG
				found = true;
#endif
			}
		}
#ifndef NDEBUG
		MAssert(found);
#endif

	}
}

// Calculate minimum and maximum value considering optimal values for the watched literals in the CURRENT interpretation
// Also returns the unknown literal with the most effect on that value
minmaxOptimAndPessBounds GenPWAgg::calculateBoundsOfWatches(GenPWatch*& largest) const {
	auto bounds = minmaxOptimAndPessBounds(getBoundsOnEmptyInterpr());
	for (auto i = getWS().cbegin(); i < getWS().cend(); ++i) {
		auto wl = (*i)->getWL();
		auto val = value(wl.getLit());
		if (val == l_Undef) {
			if (largest == NULL || largest->getWL().getWeight() < wl.getWeight()) {
				largest = *i;
			}
		}

		auto inset = val == l_True || (val == l_Undef && (*i)->isMonotone());
		addValue(getType(), wl.getWeight(), inset, bounds.optim);
		if (val != l_Undef) {
			addValue(getType(), wl.getWeight(), val == l_True, bounds.pess);
		}
	}
	return bounds;
}

void GenPWAgg::notifyFirstPropagation(const Lit& firstprop) {
	getSet().acceptForBacktrack();
	auto currentlevel = getSet().getPCSolver().getCurrentDecisionLevel();
	if (backtracklist.size() == 0) {
		backtracklist.push_back( { var(firstprop), currentlevel });
	} else if (backtracklist.back().second < currentlevel) {
		if (backtracklist.back().first != var(firstprop) || firstprop==mkPosLit(getMaxElem<int>())) {
			backtracklist.push_back( { var(firstprop), currentlevel });
		}
	} else {
		MAssert(backtracklist.back().second==currentlevel);
		backtracklist.back().first = var(firstprop);
	}
}

/**
 * @pre: pessbounds are the bounds in the CURRENT interpretation
 * @pre: calculateBoundsOfWatches AND genWatches
 *
 * NOTE: propagation only correct for positive weights!
 */
rClause GenPWAgg::checkPropagation(bool& propagations, minmaxBounds& pessbounds, Agg const * aggofprophead) {
	auto confl = nullPtrClause;

	Agg const * agg = NULL; // The current reference aggregate
	if (aggofprophead != NULL) { // the head of one aggregate was propagated
		confl = checkHeadPropagationForAgg(propagations, *aggofprophead, pessbounds);
		if(value(aggofprophead->getHead())==l_False){
			agg = aggofprophead;
		}
	} else { // A set literal was propagated, so check whether any heads can be propagated
		for (auto i = getAgg().cbegin(); confl == nullPtrClause && i < getAgg().cend(); ++i) {
			confl = checkHeadPropagationForAgg(propagations, **i, pessbounds);
		}
		agg = getAggWithMostStringentBound(false);
	}

	if (confl == nullPtrClause && agg != NULL) {
		MAssert(agg->getSem()==AggSem::OR);
		MAssert(value(agg->getHead())==l_False);
		auto lowerbound = WL(mkPosLit(1), Weight(0));
		//Calculate lowest
		if (agg->hasLB()) {
			lowerbound = WL(mkPosLit(1), getType().removeMax(pessbounds.max, agg->getBound()));
		} else {
			lowerbound = WL(mkPosLit(1), getType().removeMin(agg->getBound(), pessbounds.min));
		}
		auto i = upper_bound(getSet().getWL().cbegin(), getSet().getWL().cend(), lowerbound, compareByWeights<WL>);
		bool begin = true;
		for (; confl == nullPtrClause && i < getSet().getWL().cend(); ++i) { //INVARIANT: sorted WL
			if (begin) {
				notifyFirstPropagation(i->getLit());
			}
			begin = false;
			if (value(i->getLit()) == l_Undef) { //Otherwise would have been head conflict
				propagations = true;
				confl = getSet().notifySolver(new SetLitReason(*agg, i->getLit(), i->getWeight(), agg->hasLB()));
			}
		}
	}

	return confl;
}

rClause GenPWAgg::checkHeadPropagationForAgg(bool& propagations, const Agg& agg, const minmaxBounds& bound) {
	auto confl = nullPtrClause;
	auto propagatehead = false;
	if (agg.hasLB() && bound.max < agg.getBound()) {
		propagatehead = true;
	} else if (agg.hasUB() && agg.getBound() < bound.min) {
		propagatehead = true;
	}
	if (propagatehead) {
		propagations = true;
		confl = getSet().notifySolver(new HeadReason(agg, agg.getHead()));
		notifyFirstPropagation(agg.getHead());
	}
	return confl;
}

void GenPWAgg::genWatches(uint& i, const Agg& agg, minmaxOptimAndPessBounds& bounds, GenPWatch*& largest) {
	for (; not isSatisfied(agg, bounds.optim) && i < getNWS().size(); ++i) {
		auto watch = getNWS()[i];
		const auto& wl = watch->getWL();
		auto val = value(wl.getLit());

		bool inset = val == l_True || (val == l_Undef && watch->isMonotone());
		addValue(getType(), wl.getWeight(), inset, bounds.optim);
		if (val != l_Undef) {
			addValue(getType(), wl.getWeight(), val == l_True, bounds.pess);
		} else {
			stageWatch(watch);
			if (largest == NULL || largest->getWL().getWeight() < wl.getWeight()) {
				largest = watch;
			}
		}
	}
	MAssert(!isSatisfied(agg, bounds.pess) || isSatisfied(agg, bounds.optim));
	MAssert(isSatisfied(agg, bounds.optim) || i>=getNWS().size());
}

class wlt: public WL {
public:
	int time;
	bool inset;

	wlt()
			: WL(mkPosLit(1), Weight(0)), time(0), inset(false) {
	}
	wlt(const WL& wl, int time, bool inset)
			: WL(wl), time(time), inset(inset) {
	}
};

template<class T>
bool compareEarlier(const T& one, const T& two) {
	return one.time < two.time;
}

void GenPWAgg::getExplanation(litlist& lits, const AggReason& ar) {
	const auto& pcsol = getSet().getPCSolver();
	auto agg = ar.getAgg();
	auto head = agg.getHead();

	auto caseone = false;
	if (ar.isHeadReason()) {
		caseone = head != ar.getPropLit();
	} else {
		caseone = value(head) == l_True;
	}

	auto proplit = ar.getPropLit();
	auto conflictclause = value(ar.getPropLit()) == l_False;
	lbool headval = value(head);
	//if head known and not propagated and generating conflict clause or asserted before
	if (headval != l_Undef && var(ar.getPropLit()) != var(head) && (conflictclause || pcsol.assertedBefore(var(head), var(proplit)))) {
		lits.push_back(headval == l_True ? not head : head);
	}

	std::vector<wlt> wlis;
	for (auto i = getWS().cbegin(); i < getWS().cend(); ++i) {
		if (var((*i)->getWatchLit()) != var(proplit)) {
			auto lit = (*i)->getWL().getLit();
			if (value((*i)->getWatchLit()) == l_True) {
				wlt wli((*i)->getWL(), getSet().getPCSolver().getTime(var(lit)), (*i)->getWatchLit() == lit);
				wlis.push_back(wli);
			}
		}
	}
	for (auto i = getNWS().cbegin(); i < getNWS().cend(); ++i) {
		if (var((*i)->getWatchLit()) != var(proplit)) {
			auto lit = (*i)->getWL().getLit();
			if (value((*i)->getWatchLit()) == l_True) {
				wlt wli((*i)->getWL(), getSet().getPCSolver().getTime(var(lit)), (*i)->getWatchLit() == lit);
				wlis.push_back(wli);
			}
		}
	}

	//Follow propagation order
	sort(wlis.begin(), wlis.end(), compareEarlier<wlt>);

	auto pessbounds = getBoundsOnEmptyInterpr();
	if (!ar.isHeadReason()) { //Change value according to propagating negation of proplit
		addValue(getType(), ar.getPropWeight(), !ar.isInSet(), pessbounds);
	}

	vector<wlt> reasons;
	for (auto i = wlis.cbegin(); !isFalsified(ar.getAgg(), pessbounds) && i < wlis.cend(); ++i) {
		if (var(i->getLit()) == var(proplit)) {
			continue;
		}
		if (conflictclause || pcsol.assertedBefore(var(i->getLit()), var(proplit))) {
			addValue(getType(), i->getWeight(), i->inset, pessbounds);
			reasons.push_back(*i);
		}
	}

	//Subsetminimization
	if (getSet().modes().subsetminimizeexplanation) {
		sort(reasons.begin(), reasons.end(), compareByWeights<wlt>);
		for (auto i = reasons.begin(); i < reasons.end(); ++i) {
			removeValue(getSet().getType(), i->getWeight(), i->inset, pessbounds);
			if ((caseone && isFalsified(agg, pessbounds)) || (!caseone && isSatisfied(agg, pessbounds))) {
				i = reasons.erase(i);
				i--;
			} else {
				break;
			}
		}
	}

	for (auto i = reasons.cbegin(); i < reasons.cend(); ++i) {
		lits.push_back(value(i->getLit()) == l_True ? not i->getLit() : i->getLit());
	}

	MAssert(isFalsified(ar.getAgg(), pessbounds));
}

class TempWatch {
private:
	const WL _wl;
	const bool _watchneg;
public:
	TempWatch(const WL& wl, bool watchneg)
			: _wl(wl), _watchneg(watchneg) {
	}

	bool isMonotone() const {
		return _watchneg;
	}
	const WL& getWL() const {
		return _wl;
	}
};

double MinisatID::testGenWatchCount(const PCSolver& solver, const WLSet& set, const AggProp& type, const std::vector<TempAgg*> aggs) {
	uint totallits = set.getWL().size(), totalwatches = 0;
	std::vector<TempWatch*> nws;

	//Calculate min and max values over empty interpretation
	//Create sets and watches, initialize min/max values
	minmaxBounds emptyinterpretbounds = minmaxBounds(type.getMinPossible(set.getWL()), type.getMaxPossible(set.getWL()));
	const vwl& wls = set.getWL();
	for (uint i = 0; i < wls.size(); ++i) {
		const WL& wl = wls[i];
		bool mono = type.isMonotone(**aggs.cbegin(), wl.getWeight());
		nws.push_back(new TempWatch(wl, mono));
	}

	//Calculate reference aggregate (the one which will lead to the most watches
	auto worstagg = *aggs.cbegin();
	for (auto i = aggs.cbegin(); i < aggs.cend(); ++i) {
		if ((*i)->hasLB() && worstagg->getBound() < (*i)->getBound()) {
			worstagg = *i;
		} else if ((*i)->hasUB() && worstagg->getBound() > (*i)->getBound()) {
			worstagg = *i;
		}
	}

	bool oneagg = aggs.size() == 1;
	const auto& agg = *worstagg;

	if (oneagg && solver.value(agg.getHead()) == l_True) {
		deleteList<TempWatch>(nws);
		return 0;
	}

	minmaxOptimAndPessBounds bounds(emptyinterpretbounds);
	TempWatch* largest = NULL;
	uint i = 0;
	for (; not isSatisfied(agg, bounds.optim) && not isSatisfied(agg, bounds.pess) && i < nws.size(); ++i) {
		WL wl = nws[i]->getWL();
		lbool val = solver.value(wl.getLit());

		bool inset = val == l_True || (val == l_Undef && nws[i]->isMonotone());
		addValue(type, wl.getWeight(), inset, bounds.optim);
		if (val != l_Undef) {
			addValue(type, wl.getWeight(), val == l_True, bounds.pess);
		}

		if (val != l_False) { //Add to watches
			if (largest == NULL || largest->getWL().getWeight() < wl.getWeight()) {
				largest = nws[i];
			}
			totalwatches++;
		}
	}

	//if head was unknown before method start, at most head can have been propagated
	//so do not have to find second supporting ws
	if ((!oneagg || solver.value(agg.getHead()) != l_Undef) && (largest != NULL && not isSatisfied(agg, bounds.pess))) {
		removeValue(type, largest->getWL().getWeight(), largest->isMonotone(), bounds.optim);

		//Again until satisfied IMPORTANT: continue from previous index!
		for (; not isSatisfied(agg, bounds.optim) && not isSatisfied(agg, bounds.pess) && i < nws.size(); ++i) {
			WL wl = nws[i]->getWL();
			lbool val = solver.value(wl.getLit());

			bool inset = val == l_True || (val == l_Undef && nws[i]->isMonotone());
			addValue(type, wl.getWeight(), inset, bounds.optim);
			if (val != l_Undef) {
				addValue(type, wl.getWeight(), val == l_True, bounds.pess);
			}

			if (val != l_False) { //Add to watches
				if (largest->getWL().getWeight() < wl.getWeight()) {
					largest = nws[i];
				}
				totalwatches++;
			}
		}
	}

	deleteList<TempWatch>(nws);
	return ((double) totalwatches) / totallits;
}
