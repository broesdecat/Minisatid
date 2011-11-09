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

#include <cstdint>
#include <cinttypes>
#include <climits>
#include <set>

using namespace std;
using namespace MinisatID;

/**
 * TODO sorted aggr?
 * TODO maximum aggregate?
 */

GenPWAgg::GenPWAgg(TypedSet* set)
		: AggPropagator(set), emptyinterpretbounds(Weight(0), Weight(0)){
}

GenPWAgg::~GenPWAgg(){
	deleteList<GenPWatch>(ws);
	deleteList<GenPWatch>(nws);
}

void GenPWAgg::stageWatch(GenPWatch* watch){
	getStagedWatches().push_back(watch);
}

const agglist& GenPWAgg::getAgg() const{
	return getSet().getAgg();
}

const AggProp& GenPWAgg::getType() const{
	return getSet().getType();
}

void GenPWAgg::moveFromTo(GenPWatch* watch, genwatchlist& from, genwatchlist& to){
	if(from.size()>1){
		vsize index = watch->getIndex();
		from[index] = from[from.size()-1];
		from[index]->setIndex(index);
	}
	from.pop_back();

	to.push_back(watch);
	watch->setIndex(to.size()-1);
	watch->movedToOther();

#ifdef DEBUG
	assert(getNWS().size()+getWS().size()==getSet().getWL().size());
#endif
}

void GenPWAgg::moveFromNWSToWS(GenPWatch* watch){
	moveFromTo(watch, getNWS(), getWS());
}

void GenPWAgg::moveFromWSToNWS(GenPWatch* watch){
	moveFromTo(watch, getWS(), getNWS());
}

void GenPWAgg::addWatchToNetwork(GenPWatch* watch){
	assert(watch->isInWS());
	if(!watch->isInNetwork()){
		watch->addToNetwork();
		getSet().getPCSolver().accept(watch);
	}
}

void GenPWAgg::resetStagedWatches(int startindex){
	getStagedWatches().erase(getStagedWatches().begin()+startindex, getStagedWatches().end());
}

void GenPWAgg::addStagedWatchesToNetwork(){
	for(genwatchlist::const_iterator i=getStagedWatches().cbegin(); i<getStagedWatches().cend(); ++i){
		if(not (*i)->isInWS()){
			moveFromNWSToWS(*i);
		}
		if(not (*i)->isInNetwork()){
			addWatchToNetwork(*i);
		}
	}
	getStagedWatches().clear();
}

Agg* GenPWAgg::getAggWithMostStringentBound(bool includeunknown) const {
	Agg* strongestagg = NULL;
	for(auto i=getAgg().cbegin(); i<getAgg().cend(); ++i){
		// FIXME review this code?
		bool relevantagg = (*i)->getSem()==COMP;
		if(includeunknown){
			relevantagg |= value((*i)->getHead())!=l_True;
		}else{
			relevantagg |= value((*i)->getHead())==l_False;
		}
		//Otherwise, the aggregate does not have to hold (IMPLICATION!)
		if(relevantagg){
			if(strongestagg==NULL){
				strongestagg = *i;
			}else if(strongestagg->hasLB() && strongestagg->getCertainBound()<(*i)->getCertainBound()){
				strongestagg = *i;
			}else if(strongestagg->hasUB() && strongestagg->getCertainBound()>(*i)->getCertainBound()){
				strongestagg = *i;
			}
		}
	}
	return strongestagg;
}

// Calculate minimum and maximum value considering optimal (or the already fixed) valuesfor the watched literals
// Also returns the unknown literal with the most effect on that value
minmaxOptimAndPessBounds GenPWAgg::calculateBoundsOfWatches(GenPWatch*& largest) const {
	minmaxOptimAndPessBounds bounds(getBoundsOnEmptyInterpr());
	for(genwatchlist::const_iterator i=getWS().cbegin(); i<getWS().cend(); ++i){
		const WL& wl = (*i)->getWL();
		lbool val = value(wl.getLit());
		if(val==l_Undef){
			if(largest==NULL || largest->getWL().getWeight() < wl.getWeight()){
				largest = *i;
			}
		}

		bool inset = val==l_True || (val==l_Undef && (*i)->isMonotone());
		addValue(getType(), wl.getWeight(), inset, bounds.optim);
		if(val!=l_Undef){
			addValue(getType(), wl.getWeight(), val==l_True, bounds.pess);
		}
	}
	return bounds;
}

//@pre: min and max are the bounds considering the known values of all set literals
//	==> calc calculateBoundsOfWatches AND genWatches before checkpropagation!
rClause GenPWAgg::checkPropagation(bool& propagations, minmaxBounds& pessbounds, Agg const * aggofprophead){
	rClause confl = nullPtrClause;

	Agg const * aggp = NULL;
	if(aggofprophead!=NULL){ //aggregate head was propagated
		confl = checkHeadPropagationForAgg(propagations, *aggofprophead, pessbounds);
		aggp = aggofprophead;
	}else{
		for(agglist::const_iterator i=getAgg().cbegin(); confl==nullPtrClause && i<getAgg().cend(); ++i){
			confl = checkHeadPropagationForAgg(propagations, **i, pessbounds);
		}
		aggp = getAggWithMostStringentBound(false);
	}

	if(confl==nullPtrClause && aggp!=NULL){
		const Agg& agg = *aggp;
		WL lowerbound(mkPosLit(1), Weight(0));
		//Calculate lowes
		if(agg.hasLB()){
			lowerbound = WL(mkPosLit(1), getType().removeMax(pessbounds.max, agg.getCertainBound()));
		}else{
			lowerbound = WL(mkPosLit(1), getType().removeMin(agg.getCertainBound(), pessbounds.min));
		}
		vwl::const_iterator i = upper_bound(getSet().getWL().cbegin(), getSet().getWL().cend(), lowerbound, compareByWeights<WL>);
		for(; confl==nullPtrClause && i<getSet().getWL().cend(); ++i){ //INVARIANT: sorted WL
			if(value(i->getLit())==l_Undef){ //Otherwise would have been head conflict
				propagations = true;
				confl = getSet().notifySolver(new SetLitReason(agg, i->getLit(), i->getWeight(), agg.hasLB()));
			}
		}
	}

	return confl;
}

rClause GenPWAgg::checkHeadPropagationForAgg(bool& propagations, const Agg& agg, const minmaxBounds& bound){
	rClause confl=nullPtrClause;

	bool propagatehead = false;
	if(agg.hasLB() && bound.max<agg.getCertainBound()){
		propagatehead = true;
	}else if(agg.hasUB() && agg.getCertainBound()<bound.min){
		propagatehead = true;
	}
	if(propagatehead){
		propagations = true;
		confl = getSet().notifySolver(new HeadReason(agg, agg.getHead()));
	}

	return confl;
}

minmaxBounds GenPWAgg::calculatePessimisticBounds(){
	minmaxBounds pessbounds(getBoundsOnEmptyInterpr());
	for(vwl::const_iterator i=getSet().getWL().cbegin(); i<getSet().getWL().cend(); ++i){
		const WL& wl = *i;
		lbool val = value(wl.getLit());
		if(val==l_True){
			pessbounds.min = getType().add(pessbounds.min, wl.getWeight());
		}else if(val==l_False){
			pessbounds.max = getType().removeMax(pessbounds.max, wl.getWeight());
		}
	}
	return pessbounds;
}

void GenPWAgg::checkInitiallyKnownAggs(bool& unsat, bool& sat){
	minmaxBounds pessbounds = calculatePessimisticBounds();

	rClause confl = nullPtrClause;
	std::set<Agg*> del;
	for(auto i=getAgg().cbegin(); confl==nullPtrClause && i<getAgg().cend(); ++i){
		if((*i)->isOptimAgg()){
			continue;
		}
		if(value((*i)->getHead())==l_True){ //Head always true
			del.insert(*i);
		}else if(isSatisfied(**i, pessbounds)){ // Agg always true
			del.insert(*i);
		}else if(isFalsified(**i, pessbounds)){ // Agg always false
			confl = getSet().notifySolver(new HeadReason(**i, (*i)->getHead()));
			del.insert(*i);
		}
	}
	getSet().removeAggs(del);
	if(confl!=nullPtrClause){
		unsat = true;
	}else if(getAgg().size()==0){
		sat = true;
	}
}

/**
 * @pre All aggregates have the same sign and implication instead of equivalence, head can be negative!
 * initialize NWS: make a watch for each set literal, watch the negation of the set literal if its monotone
 *					then reconstruct the set for the aggregate with the lowest bound!
 */
void GenPWAgg::initialize(bool& unsat, bool& sat) {
#ifdef DEBUG
	assert(getAgg().size()>0);
	assert(unsat==false && sat==false);
	const agglist& aggs = getAgg();
	AggSign sign = aggs[0]->getSign();
	for(auto i=aggs.cbegin(); i<aggs.cend(); ++i){
		assert((*i)->getSign()==sign);
		assert((*i)->getSem()==IMPLICATION);
	}
#endif

	TypedSet& set = getSet();
	const vwl& wls = set.getWL();

	setBoundsOnEmptyInterpr(minmaxBounds(getType().getMinPossible(set), getType().getMaxPossible(set)));

	// Create watches
	for(auto i=wls.rbegin(); i<wls.rend(); ++i){
		bool mono = getType().isMonotone(**getAgg().cbegin(), i->getWeight());
		nws.push_back(new GenPWatch(getSetp(), *i, mono, nws.size()));
	}

	// Check initial derivations
	checkInitiallyKnownAggs(unsat, sat);
	if(unsat || sat){
		return;
	}

	// Calculate reference aggregate (the one which will lead to the most watches)
	worstagg = getAggWithMostStringentBound(true);
	assert(worstagg != NULL);

	// Construct first watches
	bool propagations = false;
	rClause confl = reconstructSet(NULL, propagations, NULL);
	if(confl!=nullPtrClause){
		unsat = true; return;
	}

	addStagedWatchesToNetwork();
	AggPropagator::initialize(unsat, sat);
}

rClause GenPWAgg::reInitialize() {
	bool propagations = false;
	rClause confl = reconstructSet(NULL, propagations, NULL);
	if(confl==nullPtrClause){
		confl = propagateAtEndOfQueue();
	}
	return confl;
}

/**
 * do propagation, both body and heads:
 * 		calc full min and max
 * reconstruct watches:
 * 		calc min and max of watched set and store largest non-false weight
 * 		keep adding non-false until satisfied
 * 		if head known
 * 			remove largest, keep adding non-false until satisfied
 */
rClause GenPWAgg::reconstructSet(GenPWatch* watch, bool& propagations, Agg const * propagg){
#ifdef DEBUG
	for(auto i=getSet().getWL().cbegin(); i<getSet().getWL().cend(); ++i){
		bool found = false;
		for(auto j=getNWS().cbegin(); j<getNWS().cend(); ++j){
			if(var(i->getLit())==var((*j)->getWL().getLit())){
				found = true;
			}
		}
		for(auto j=getWS().cbegin(); j<getWS().cend(); ++j){
			if(var(i->getLit())==var((*j)->getWL().getLit())){
				found = true;
			}
		}
		assert(found);
	}
#endif

	rClause confl = nullPtrClause;
	bool oneagg = getAgg().size()==1;

	//possible HACK: watch all at all times
	/*for(int i=0 ;i<getNWS().size(); ++i){
		stageWatch(getNWS()[i]);
	}*/

	//possible HACK: always keep watch
	//propagations = true;

	if(oneagg && value((*getAgg().cbegin())->getHead())==l_True){
		return confl;
	}

	vsize nwsindex = 0;
	GenPWatch* largestunkn = NULL;
	const Agg& worstagg = *getWorstAgg();
	minmaxOptimAndPessBounds bounds = calculateBoundsOfWatches(largestunkn);

	genWatches(nwsindex, worstagg, bounds, largestunkn);

	if(!isSatisfied(worstagg, bounds.optim)){
		// can certainly propagate head
		return checkPropagation(propagations, bounds.pess, propagg);
	}else if(oneagg && value((*getAgg().cbegin())->getHead())==l_Undef){
		// if head is still unknown, one ws suffices
		return confl;
	}else if(largestunkn==NULL || isSatisfied(worstagg, bounds.pess)){
		// certainly satisfied: no more watches needed, but do not delete the current ones!
		propagations = true;
		return confl;
	}

	vsize storednwsindex = nwsindex, storedstagedindex = getStagedWatches().size();
	minmaxOptimAndPessBounds storedbounds = bounds;

	//Leave out largest
	assert(largestunkn!=NULL);
	removeValue(getType(), largestunkn->getWL().getWeight(), largestunkn->isMonotone(), bounds.optim);

	genWatches(nwsindex, worstagg, bounds, largestunkn);

	if(!isSatisfied(worstagg, bounds.optim)){
		confl = checkPropagation(propagations, bounds.pess, propagg);
		if(confl!=nullPtrClause){
			propagations = true;
			return confl;
		}

		//TODO can it be done cheaper?
		resetStagedWatches(storedstagedindex);
		bounds = storedbounds;
		//FIXME Recalculate largest (can have decreased)
		nwsindex = storednwsindex;
		genWatches(nwsindex, worstagg, bounds, largestunkn);
	}

#ifdef DEBUG
	for(vwl::const_iterator i=getSet().getWL().cbegin(); i<getSet().getWL().cend(); ++i){
		bool found = false;
		for(genwatchlist::const_iterator j=getNWS().cbegin(); j<getNWS().cend(); ++j){
			if(var(i->getLit())==var((*j)->getWL().getLit())){
				found = true;
			}
		}
		for(genwatchlist::const_iterator j=getWS().cbegin(); j<getWS().cend(); ++j){
			if(var(i->getLit())==var((*j)->getWL().getLit())){
				found = true;
			}
		}
		assert(found);
	}
#endif

	return confl;
}

void GenPWAgg::genWatches(vsize& i, const Agg& agg, minmaxOptimAndPessBounds& bounds, GenPWatch*& largest){
	for(;!isSatisfied(agg, bounds.optim) && i<getNWS().size(); ++i){
		GenPWatch* watch = getNWS()[i];
		WL wl = watch->getWL();
		lbool val = value(wl.getLit());

		bool inset = val==l_True || (val==l_Undef && watch->isMonotone());
		addValue(getType(), wl.getWeight(), inset, bounds.optim);
		if(val!=l_Undef){
			addValue(getType(), wl.getWeight(), val==l_True, bounds.pess);
		}

		if((watch->isMonotone() && val!=l_False) || (!watch->isMonotone() && val!=l_True)){
			stageWatch(watch);

			if(largest==NULL || largest->getWL().getWeight() < wl.getWeight()){
				largest = watch;
			}
		}
	}
	assert(!isSatisfied(agg, bounds.pess) || isSatisfied(agg, bounds.optim));
	assert(isSatisfied(agg, bounds.optim) || i>=getNWS().size());
}

void GenPWAgg::propagate(int level, Watch* ws, int aggindex){
	trail.push_back(ws);
	getSet().getPCSolver().acceptForBacktrack(getSetp());
}
void GenPWAgg::propagate(const Lit& p, Watch* ws, int level){
	trail.push_back(ws);
	getSet().getPCSolver().acceptForBacktrack(getSetp());
}

rClause GenPWAgg::propagateAtEndOfQueue(Watch* watch) {
	rClause confl = nullPtrClause;
	GenPWatch* const pw = dynamic_cast<GenPWatch*>(watch);

	// Before calling propagate, the watch should have been removed from the network datastructure
	// but should still think it is in (which we fix here)
	assert(pw->isInNetwork());
	pw->removeFromNetwork();

	if(!pw->isInWS()){ //Already in NWS, so no need to watch it
		assert(getNWS()[pw->getIndex()]==pw); //Check it really is in NWS
		return confl;
	}

	//Now, it should be in WS and know this
	assert(getWS()[pw->getIndex()]==pw);

	bool propagations = false;
	confl = reconstructSet(pw, propagations, NULL);

	if(!propagations && confl==nullPtrClause){ //It can be safely removed as a watch
		moveFromWSToNWS(pw);
	}else{ //Otherwise, add it again to the network
		stageWatch(pw);
	}

	if(confl!=nullPtrClause){
		resetStagedWatches();
	}else{
		addStagedWatchesToNetwork();
	}

	assert(!pw->isInWS() || getWS()[pw->getIndex()]==pw);
	return confl;
}

rClause GenPWAgg::propagateAtEndOfQueue(const Agg& agg) {
	bool propagations = false;
	rClause confl = reconstructSet(NULL, propagations, &agg);
	addStagedWatchesToNetwork();
	return confl;
}

// NOOP because all propagation is done in propagate
rClause	GenPWAgg::propagateAtEndOfQueue(){
	rClause confl = nullPtrClause;
	for(vsize i=0; confl == nullPtrClause && i<trail.size(); ++i){
		auto watch = trail[i];
		if(watch->headWatch()){
			confl = propagateAtEndOfQueue(*getAgg()[watch->getAggIndex()]);
		}else{
			confl = propagateAtEndOfQueue(watch);
		}
	}
	trail.clear();
	return confl;
}

class wlt: public WL{
public:
	int time;
	bool inset;

	wlt(): WL(createPositiveLiteral(1), Weight(0)), time(0), inset(false){}
	wlt(const WL& wl, int time, bool inset): WL(wl), time(time), inset(inset){}
};

template<class T>
bool compareEarlier(const T& one, const T& two){
	return one.time < two.time;
}

void GenPWAgg::getExplanation(litlist& lits, const AggReason& ar) {
	const PCSolver& pcsol = getSet().getPCSolver();
	const Agg& agg = ar.getAgg();
	const Lit& head = agg.getHead();

	bool caseone = false;
	if(ar.isHeadReason()){
		caseone = head!=ar.getPropLit();
	}else{
		caseone = value(head)==l_True;
	}

	const Lit& proplit = ar.getPropLit();
	bool conflictclause = value(ar.getPropLit())==l_False;
	lbool headval = value(head);
	//if head known and not propagated and generating conflict clause or asserted before
	if(headval!=l_Undef && var(ar.getPropLit())!=var(head) &&
			(conflictclause || pcsol.assertedBefore(var(head), var(proplit)))){
		lits.push_back(headval==l_True?not head:head);
	}

	std::vector<wlt> wlis;
	for(auto i=getWS().cbegin(); i<getWS().cend(); ++i){
		if(var((*i)->getWatchLit())!=var(proplit)){
			const Lit& lit = (*i)->getWL().getLit();
			if(value((*i)->getWatchLit())==l_True){
				wlt wli((*i)->getWL(), getSet().getPCSolver().getTime(var(lit)), (*i)->getWatchLit()==lit);
				wlis.push_back(wli);
			}
		}
	}
	for(genwatchlist::const_iterator i=getNWS().cbegin(); i<getNWS().cend(); ++i){
		if(var((*i)->getWatchLit())!=var(proplit)){
			const Lit& lit = (*i)->getWL().getLit();
			if(value((*i)->getWatchLit())==l_True){
				wlt wli((*i)->getWL(), getSet().getPCSolver().getTime(var(lit)), (*i)->getWatchLit()==lit);
				wlis.push_back(wli);
			}
		}
	}

	//Follow propagation order
	sort(wlis.begin(), wlis.end(), compareEarlier<wlt>);

	minmaxBounds pessbounds(getBoundsOnEmptyInterpr());
	if(!ar.isHeadReason()){ //Change value according to propagating negation of proplit
		addValue(getType(), ar.getPropWeight(), !ar.isInSet(), pessbounds);
	}

	vector<wlt> reasons;
	for(auto i=wlis.cbegin(); !isFalsified(ar.getAgg(), pessbounds) && i<wlis.cend(); ++i){
		if(var(i->getLit())==var(proplit)){
			continue;
		}
		if(conflictclause || pcsol.assertedBefore(var(i->getLit()), var(proplit))){
			addValue(getType(), i->getWeight(), i->inset, pessbounds);
			reasons.push_back(*i);
		}
	}

	//Subsetminimization
	if(getSet().modes().subsetminimizeexplanation){
		sort(reasons.begin(), reasons.end(), compareByWeights<wlt>);
		for(auto i=reasons.begin(); i<reasons.end(); ++i){
			removeValue(getSet().getType(), i->getWeight(), i->inset, pessbounds);
			if((caseone && isFalsified(agg, pessbounds) ) ||(!caseone && isSatisfied(agg, pessbounds))){
				i = reasons.erase(i);
				i--;
			}else{
				break;
			}
		}
	}

	for(auto i=reasons.cbegin(); i<reasons.cend(); ++i){
		lits.push_back(value(i->getLit())==l_True?not i->getLit():i->getLit());
	}

	assert(isFalsified(ar.getAgg(), pessbounds));
}

class TempWatch{
private:
	const 	WL		_wl;
	const 	bool	_watchneg;
public:
	TempWatch(const WL& wl, bool watchneg):
		_wl(wl),
		_watchneg(watchneg){
	}

	bool 		isMonotone	()	const 	{ return _watchneg; }
	const WL& 	getWL		() 	const 	{ return _wl; }
};

double MinisatID::testGenWatchCount(const PCSolver& solver, const InnerWLSet& set, const AggProp& type, const std::vector<TempAgg*> aggs, const Weight& knownbound) {
	int totallits = set.wls.size(), totalwatches = 0;
	std::vector<TempWatch*> nws;
	TempAgg const * worstagg;

	//Calculate min and max values over empty interpretation
	//Create sets and watches, initialize min/max values
	minmaxBounds emptyinterpretbounds = minmaxBounds(type.getMinPossible(set.getWL()), type.getMaxPossible(set.getWL()));
	const vwl& wls = set.getWL();
	for(vsize i=0; i<wls.size(); ++i){
		const WL& wl = wls[i];
		bool mono = type.isMonotone(**aggs.cbegin(), wl.getWeight(), knownbound);
		nws.push_back(new TempWatch(wl, mono));
	}

	//Calculate reference aggregate (the one which will lead to the most watches
	worstagg = *aggs.cbegin();
	for(auto i=aggs.cbegin(); i<aggs.cend(); ++i){
		if((*i)->hasLB() && worstagg->getBound()<(*i)->getBound()){
			worstagg = *i;
		}else if((*i)->hasUB() && worstagg->getBound()>(*i)->getBound()){
			worstagg = *i;
		}
	}

	bool oneagg = aggs.size()==1;
	const TempAgg& agg = *worstagg;

	if(oneagg && solver.value(agg.getHead())==l_True){
		return 0;
	}

	minmaxOptimAndPessBounds bounds(emptyinterpretbounds);
	TempWatch* largest = NULL;
	vsize i = 0;
	for(;!isSatisfied(agg, bounds.optim, knownbound) && !isSatisfied(agg, bounds.pess, knownbound) && i<nws.size(); ++i){
		WL wl = nws[i]->getWL();
		lbool val = solver.value(wl.getLit());

		bool inset = val==l_True || (val==l_Undef && nws[i]->isMonotone());
		addValue(type, wl.getWeight(), inset, bounds.optim);
		if(val!=l_Undef){
			addValue(type, wl.getWeight(), val==l_True, bounds.pess);
		}

		if(val!=l_False){ //Add to watches
			if(largest==NULL || largest->getWL().getWeight() < wl.getWeight()){
				largest = nws[i];
			}
			totalwatches++;
		}
	}

	//if head was unknown before method start, at most head can have been propagated
	//so do not have to find second supporting ws
	if((!oneagg || solver.value(agg.getHead())!=l_Undef) && (largest!=NULL && !isSatisfied(agg, bounds.pess, knownbound))){
		removeValue(type, largest->getWL().getWeight(), largest->isMonotone(), bounds.optim);

		//Again until satisfied IMPORTANT: continue from previous index!
		for(; !isSatisfied(agg, bounds.optim, knownbound) && !isSatisfied(agg, bounds.pess, knownbound) && i<nws.size(); ++i){
			WL wl = nws[i]->getWL();
			lbool val = solver.value(wl.getLit());

			bool inset = val==l_True || (val==l_Undef && nws[i]->isMonotone());
			addValue(type, wl.getWeight(), inset, bounds.optim);
			if(val!=l_Undef){
				addValue(type, wl.getWeight(), val==l_True, bounds.pess);
			}

			if(val!=l_False){ //Add to watches
				if(largest->getWL().getWeight() < wl.getWeight()){
					largest = nws[i];
				}
				totalwatches++;
			}
		}
	}

	double ratio = ((double)totalwatches)/totallits;
	return ratio;
}
