#include "solvers/aggsolver/AggComb.hpp"

#include "solvers/aggsolver/AggSolver.hpp"
#include "solvers/pcsolver/PCSolver.hpp"

#include <algorithm>

using namespace Aggrs;

AggSet::AggSet(const vector<WL>& wl) {
	wlits.insert(wlits.begin(), wl.begin(), wl.end());
	std::sort(wlits.begin(), wlits.end());
}

void AggSet::setWL(const vector<WL>& newset) {
	wlits = newset;
	//important to sort again to guarantee that it is sorted according to the weights
	std::sort(wlits.begin(), wlits.end());
}

CalcAgg::CalcAgg(const paggsol& solver, const vector<WL>& wl) :
	aggsolver(solver), set(new AggSet(wl)), emptysetvalue(0) {
}

bool MaxAggT::isMonotone(const Agg& agg, const WL& l) const {
	return (agg.isLower() && l.getWeight() <= agg.getLowerBound()) || (agg.isUpper());
}

bool SumAggT::isMonotone(const Agg& agg, const WL& l) const {
	return (agg.isLower() && l.getWeight() < 0) || (agg.isUpper() && l.getWeight() > 0);
}

bool ProdAggT::isMonotone(const Agg& agg, const WL& l) const {
	assert(l.getWeight() == 0 || l.getWeight() >= 1);
	return agg.isUpper();
}

void CalcAgg::addAgg(pagg aggr) {
	aggregates.push_back(aggr);
	aggr->setComb(this, aggregates.size() - 1);
}

/*AggComb::AggComb(const AggComb& comb){
 aggregates = comb.getAgg();
 set = comb.getSet();
 aggsolver = comb.getSolver();
 emptysetvalue = comb.getESV();
 }*/

CalcAgg::~CalcAgg() {
	deleteList<Agg> (aggregates);
	delete set;
	delete prop;
}

Propagator::Propagator(paggs agg): agg(agg) {
}

MaxCalc::MaxCalc(const paggsol& solver, const vwl& wl):
	CalcAgg(solver, wl){
	//FIXME moet eigenlijk een voorstelling van -infinity zijn
	//ik had eerst: |minimum van de set| -1, maar de bound zelf kan NOG lager liggen, dus dan is het fout
	setESV(Weight(INT_MIN));
	assert(getESV() <= INT_MIN);

	prop = new MaxFWAgg(this);
}

SumCalc::SumCalc(const paggsol& solver, const vwl& wl):
	CalcAgg(solver, wl){
	setESV(0);
	prop = new SumFWAgg(this);
}

ProdCalc::ProdCalc(const paggsol& solver, const vwl& wl):
	CalcAgg(solver, wl){
	setESV(1);
	prop = new ProdFWAgg(this);
}

CardCalc::CardCalc(const paggsol& solver, const vwl& wl):
	CalcAgg(solver, wl){
	setESV(0);
	prop = new SumFWAgg(this);
}

/*
 * Allow sorting of WL, getting same literals next to each other
 */
bool compareLits(const WL& one, const WL& two) {
	return var(one.getLit()) < var(two.getLit());
}

/**
 * Checks whether the same literal occurs multiple times in the set
 * If this is the case, all identical literals are combined into one.
 *
 * @post: the literals are sorted according to weight again
 */
void CalcAgg::doSetReduction() {
	vwl oldset = getSet()->getWL();
	vwl newset;


	//Sort all wlits according to the integer representation of their literal (to get all literals next to each other)
	std::sort(oldset.begin(), oldset.end(), compareLits);

	int indexinnew = 0;
	newset.push_back(oldset[indexinnew]);

	bool setisreduced = false;
	for (vwl::size_type i = 1; i < oldset.size(); i++) {
		WL oldl = newset[indexinnew];
		WL newl = oldset[i];
		if (var(oldl.getLit()) == var(newl.getLit())) { //same variable
			setisreduced = true;
			if (oldl.getLit() == newl.getLit()) { //same literal, keep combined weight
				Weight w = getCombinedWeight(newl.getWeight(), oldl.getWeight());
				newset[indexinnew] = WL(oldl.getLit(), w);
			} else { //opposite signs
				WL wl = handleOccurenceOfBothSigns(oldl, newl);
				newset[indexinnew] = WL(wl.getLit(), wl.getWeight());
			}
		} else {
			newset.push_back(newl);
			indexinnew++;
		}
	}

	vwl newset2;
	for (vwl::size_type i = 0; i < newset.size(); i++) {
		if (!isNeutralElement(newset[i].getWeight())) {
			newset2.push_back(newset[i]);
		} else {
			setisreduced = true;
		}
	}

	if (setisreduced) {
		getSet()->setWL(newset2);
	}
}

bool CalcAgg::canJustifyHead(
								const Agg& agg,
								vec<Lit>& jstf,
								vec<Var>& nonjstf,
								vec<int>& currentjust,
								bool real) const {
	prop->canJustifyHead(agg, jstf, nonjstf, currentjust, real);
}
// Propagate set literal
rClause CalcAgg::propagate(const Lit& p, const Watch& w) {
	prop->propagate(p, w);
}
// Propagate head
rClause CalcAgg::propagate(const Agg& agg) {
	prop->propagate(agg);
}
// Backtrack set literal
void CalcAgg::backtrack(const Watch& w) {
	prop->backtrack(w);
}
// Backtrack head
void CalcAgg::backtrack(const Agg& agg) {
	prop->backtrack(agg);
}

void CalcAgg::getExplanation(vec<Lit>& lits, const AggReason& ar) const {
	prop->getExplanation(lits, ar);
}

///////
// SUM CALC
///////

Weight SumCalc::getBestPossible() const {
	Weight max = getESV();
	for (vwl::const_iterator j = getWL().begin(); j < getWL().end(); j++) {
		max = this->add(max, (*j).getWeight());
	}
	return max;
}

Weight SumAggT::add(const Weight& lhs, const Weight& rhs) const {
#ifdef INTWEIGHT
	if(lhs>0 && rhs > 0 && INT_MAX-lhs < rhs) {
		return INT_MAX;
	} else if(lhs<0 && rhs<0 && INT_MIN-lhs>rhs) {
		return INT_MIN;
	}
#endif
	return lhs + rhs;
}

Weight SumAggT::remove(const Weight& lhs, const Weight& rhs) const {
	return lhs - rhs;
}

Weight SumCalc::getCombinedWeight(const Weight& one, const Weight& two) const {
	return this->add(one, two);
}

WL SumCalc::handleOccurenceOfBothSigns(const WL& one, const WL& two) {
	if (one.getWeight() < two.getWeight()) {
		setESV(getESV() + one.getWeight());
		return WL(two.getLit(), this->remove(two.getWeight(), one.getWeight()));
	} else {
		setESV(getESV() + two.getWeight());
		return WL(one.getLit(), this->remove(one.getWeight(), two.getWeight()));
	}
}

///////
// CARD CALC
///////

Weight CardCalc::getBestPossible() const {
	Weight max = getESV();
	for (vwl::const_iterator j = getWL().begin(); j < getWL().end(); j++) {
		max = this->add(max, (*j).getWeight());
	}
	return max;
}

Weight CardAggT::add(const Weight& lhs, const Weight& rhs) const {
#ifdef INTWEIGHT
	if(lhs>0 && rhs > 0 && INT_MAX-lhs < rhs) {
		return INT_MAX;
	} else if(lhs<0 && rhs<0 && INT_MIN-lhs>rhs) {
		return INT_MIN;
	}
#endif
	return lhs + rhs;
}

Weight CardAggT::remove(const Weight& lhs, const Weight& rhs) const {
	return lhs - rhs;
}

Weight CardCalc::getCombinedWeight(const Weight& one, const Weight& two) const {
	return this->add(one, two);
}

WL CardCalc::handleOccurenceOfBothSigns(const WL& one, const WL& two) {
	if (one.getWeight() < two.getWeight()) {
		setESV(getESV() + one.getWeight());
		return WL(two.getLit(), this->remove(two.getWeight(), one.getWeight()));
	} else {
		setESV(getESV() + two.getWeight());
		return WL(one.getLit(), this->remove(one.getWeight(), two.getWeight()));
	}
}

///////
// MAX CALC
///////

Weight MaxCalc::getBestPossible() const {
	return getWL().back().getWeight();
}

Weight MaxCalc::getCombinedWeight(const Weight& first, const Weight& second) const {
	return first > second ? first : second;
}

WL MaxCalc::handleOccurenceOfBothSigns(const WL& one, const WL& two) {
	if (one.getWeight() > two.getWeight()) {
		if (getESV() < two.getWeight()) {
			setESV(two.getWeight());
		}
		return one;
	} else {
		if (getESV() < one.getWeight()) {
			setESV(one.getWeight());
		}
		return two;
	}
}

///////
// PROD CALC
///////

Weight ProdCalc::getBestPossible() const {
	Weight max = getESV();
	for (vwl::const_iterator j = getWL().begin(); j < getWL().end(); j++) {
		max = this->add(max, (*j).getWeight());
	}
	return max;
}

Weight ProdAggT::add(const Weight& lhs, const Weight& rhs) const {
#ifdef INTWEIGHT
	bool sign = false;
	Weight l = lhs, r = rhs;
	if(l<0) {
		l= -l;
		sign = true;
	}
	if(r<0) {
		r = -r;
		sign = !sign;
	}
	if(INT_MAX/l < r) {
		return sign?INT_MIN:INT_MAX;
	}
#endif
	return lhs * rhs;
}

Weight ProdAggT::remove(const Weight& lhs, const Weight& rhs) const {
	Weight w = 0;
	if (rhs != 0) {
		w = lhs / rhs;
		if (w == 1 && lhs > rhs) {
			w = 2;
		}
	}

	return w;
}

Weight ProdCalc::getCombinedWeight(const Weight& one, const Weight& two) const {
	return this->add(one, two);
}

WL ProdCalc::handleOccurenceOfBothSigns(const WL& one, const WL& two) {
	//NOTE: om dit toe te laten, ofwel bij elke operatie op en literal al zijn voorkomens overlopen
	//ofwel aggregaten voor doubles ondersteunen (het eerste is eigenlijk de beste oplossing)
	//Mogelijke eenvoudige implementatie: weigts bijhouden als doubles (en al de rest als ints)
	reportf("Product aggregates in which both the literal and its negation occur "
		"are currently not supported. Replace ");
	gprintLit(one.getLit());
	reportf("or ");
	gprintLit(two.getLit());
	reportf("by a tseitin.\n");
	throw idpexception("Atoms in product aggregates have to be unique.\n");
}

/******
 * SPECIFIC CODE
 */

paggs CalcAgg::initialize(bool& unsat) {
	return prop->initialize(unsat);
}

// Final initialization call!
paggs Propagator::initialize(bool& unsat) {
	for (int i = 0; i < as().getAgg().size(); i++) {
		as().getSolver()->setHeadWatch(var(as().getAgg()[i]->getHead()), as().getAgg()[i]);
	}
	return asp();
}

FWAgg::FWAgg(paggs agg) :
	Propagator(agg), currentbestcertain(0), currentbestpossible(0) {

}

paggs FWAgg::initialize(bool& unsat) {
	unsat = false;
	if (as().getAgg().size() == 0) {
		return NULL;
	}
	as().doSetReduction();
	truth.resize(as().getWL().size(), l_Undef);

	setCP(as().getBestPossible());
	setCC(as().getESV());

	int startsize = as().getAgg().size();
	headvalue.resize(startsize, l_Undef);
	headindex.resize(startsize, -1);
	nomoreprops.resize(startsize, false);
	optimagg.resize(startsize, false);
	headproptime.resize(startsize, -1);
	headprop.resize(startsize, false);

	int i = 0, j = 0;
	for (; !unsat && i < as().getAgg().size(); i++) {
		pagg agg = as().getAgg()[i];
		lbool result = initialize(*agg);
		if (result == l_True && !agg->isDefined()) {
			//If after initialization, the head will have a fixed value, then this is
			//independent of any further propagations within that aggregate.
			//BUT ONLY if it is not defined (or at a later stage, if it cannot be in any loop
			as().getSolver()->removeHeadWatch(var(agg->getHead()));
			delete agg;
		} else if (result == l_False) {
			unsat = true; //UNSAT because always false
			return NULL;
		} else {
			agg->setIndex(j);
			as().getRefAgg()[j++] = agg;
		}
	}
	as().getRefAgg().resize(j);
	headvalue.resize(j, l_Undef);
	headindex.resize(j, -1);
	nomoreprops.resize(j, false);
	optimagg.resize(j, false);
	headproptime.resize(j, -1);
	headprop.resize(j, false);

	for (int j = 0; j < as().getWL().size(); j++) {
		const Lit& l = as().getWL()[j].getLit();
		Var v = var(l);
		as().getSolver()->addPermWatch(v, new Watch(agg, j, true, sign(l) ? false : true));
	}

	return Propagator::initialize(unsat);
}

/**
 * Returns true if this aggregate can be propagated in the initialization, so it will never change truth value
 * and can be left out of any propagations.
 */
lbool FWAgg::initialize(const Agg& agg) {
	rClause confl = nullPtrClause;

	lbool hv = canPropagateHead(agg, getCC(), getCP());
	bool alwaystrue = false;
	if (hv != l_Undef && !optimagg[agg.getIndex()]) {
		alwaystrue = true;
		//reportf("No more propagations for %d", gprintVar(var(head)));
	}
	if (hv == l_True) {
		confl = as().getSolver()->notifySATsolverOfPropagation(agg.getHead(), new AggReason(
																						agg,
																						agg.getHead(),
																						CPANDCC,
																						true));
	} else if (hv == l_False) {
		confl = as().getSolver()->notifySATsolverOfPropagation(~agg.getHead(), new AggReason(
																						agg,
																						~agg.getHead(),
																						CPANDCC,
																						true));
	}
	if (confl != nullPtrClause) {
		return l_False;
	}

	return alwaystrue ? l_True : l_Undef;
}

void FWAgg::backtrack(const Agg& agg, int stacksize) {
	if (headprop[agg.getIndex()] && headproptime[agg.getIndex()] > stacksize) {
		headprop[agg.getIndex()] = false;
	}
}

void FWAgg::backtrack(const Agg& agg) {
	if (nomoreprops[agg.getIndex()]) {
		return;
	}

	headvalue[agg.getIndex()] = l_Undef;
	headindex[agg.getIndex()] = -1;
}

void FWAgg::backtrack(const Watch& w) {
	if (getStack().size() == 0 || var(getStack().back().getLit()) != var(as().getWL()[w.getIndex()].getLit())) {
		return; //Only backtrack if it was effectively propagated
	}
	const PropagationInfo& pi = stack.back();
	stack.pop_back();

	assert(pi.getType() != HEAD && var(pi.getLit()) == var(as().getWL()[w.getIndex()].getLit()));

	truth[w.getIndex()] = l_Undef;
	setCC(pi.getPC());
	setCP(pi.getPP());

	int s = stack.size();
	for (vpagg::const_iterator i = as().getAgg().begin(); i < as().getAgg().end(); i++) {
		backtrack(**i, s);
	}
}

/**
 * Returns non-owning pointer
 */
rClause FWAgg::propagate(const Agg& agg) {
	if (nomoreprops[agg.getIndex()] || headprop[agg.getIndex()]) {
		return nullPtrClause;
	}

	lbool headtrue = as().getSolver()->value(agg.getHead());
	headvalue[agg.getIndex()] = headtrue;
	headindex[agg.getIndex()] = getStack().size();
	rClause confl = propagate(agg, headtrue == l_True);
	return confl;
}

rClause FWAgg::propagate(const Lit& p, const Watch& ws) {
	Occurrence tp;
	if (ws.getType() == POS) {
		tp = sign(p) ? NEG : POS;
	} else {
		tp = sign(p) ? POS : NEG;
	}

	const WL& wl = as().getWL()[ws.getIndex()];
	stack.push_back(PropagationInfo(p, wl.getWeight(), tp, getCC(), getCP()));
	truth[ws.getIndex()] = tp == POS ? l_True : l_False;
	tp == POS ? addToCertainSet(wl) : removeFromPossibleSet(wl);

	rClause confl = nullPtrClause;
	for (int i = 0; i < as().getAgg().size() && confl == nullPtrClause; i++) {
		const Agg& pa = *as().getAgg()[i];

		if (as().getSolver()->verbosity() >= 4) {
			reportf("Propagating into aggr: ");
			Aggrs::printAgg(pa);
		}

		lbool hv = headvalue[pa.getIndex()];
		if (hv != l_Undef) { //head is already known
			assert(canPropagateHead(pa, getCC(), getCP()) != (hv == l_True ? l_False : l_True)); //A conflicting propagation is not possible if we have complete propagation
			confl = propagate(pa, hv == l_True);
		} else { //head is not yet known, so at most the head can be propagated
			lbool result = canPropagateHead(pa, getCC(), getCP());
			if (result != l_Undef) {
				rClause	cc =
							as().getSolver()->notifySATsolverOfPropagation(
								result == l_True ? pa.getHead() : ~pa.getHead(),
								new AggReason(pa, p, CPANDCC, true));
				confl = cc;
			}
		}
	}
	return confl;
}

lbool FWAgg::canPropagateHead(const Agg& agg, const Weight& CC, const Weight& CP) const {
	if (nomoreprops[agg.getIndex()] || headprop[agg.getIndex()]) {
		return headvalue[agg.getIndex()];
	}

	if ((agg.isLower() && CC > agg.getLowerBound()) || (agg.isUpper() && CP < agg.getUpperBound())) {
		headproptime[agg.getIndex()] = getStack().size();
		headprop[agg.getIndex()] = true;
		return l_False;
	} else if ((agg.isLower() && CP <= agg.getLowerBound()) || (agg.isUpper() && CC
				>= agg.getUpperBound())) {
		headproptime[agg.getIndex()] = getStack().size();
		headprop[agg.getIndex()] = true;
		return l_True;
	} else {
		return l_Undef;
	}
}

/**
 * Should find a set L+ such that "bigwedge{l | l in L+} implies p"
 * which is equivalent with the clause bigvee{~l|l in L+} or p
 * and this is returned as the set {~l|l in L+}
 */
void FWAgg::getExplanation(vec<Lit>& lits, const AggReason& ar) const {
	//assert(ar.getAgg() == agg);
	//assert(agg->getSet()==this);

	int index = -1;
	for (int i = 0; i < getStack().size(); i++) {
		if (getStack()[i].getLit() == ar.getLit()) {
			index = i;
			break;
		}
	}
	if (index == -1) {
		index = getStack().size();
	}
	//assert(index!=-1); //Is wrong because when a conflict is derived, an explanation is constructed before the conflicting literal is stacked.

	const Agg& agg = ar.getAgg();
	const Lit& head = agg.getHead();

	if (!ar.isHeadReason() && index >= headindex[agg.getIndex()]) {
		//the head literal is saved as it occurred in the theory, so adapt for its current truth value!
		lits.push(as().getSolver()->isTrue(head) ? ~head : head);
	}

	//assert(ar.isHeadReason() || getPCSolver()->getLevel(ar.getLit())<=s->getStackSize());

	//	This is correct, but not minimal enough. We expect to be able to do better
	//	for(lprop::const_iterator i=s->getStackBegin(); counter<ar.getIndex() && i<s->getStackEnd(); i++,counter++){
	//		lits.push(~(*i).getLit());
	//	}

	int counter = 0;
	if (ar.getExpl() != HEADONLY) {
		for (vprop::const_iterator i = getStack().begin(); counter < index && i < getStack().end(); i++, counter++) {
			//for(lprop::const_iterator i=s->getStackBegin(); var(ar.getLit())!=var((*i).getLit()) && i<s->getStackEnd(); i++){
			switch (ar.getExpl()) {
			case BASEDONCC:
				if ((*i).getType() == POS) {
					lits.push(~(*i).getLit());
				}
				break;
			case BASEDONCP:
				if ((*i).getType() == NEG) {
					lits.push(~(*i).getLit());
				}
				break;
			case CPANDCC:
				lits.push(~(*i).getLit());
				break;
			default:
				assert(false);
				break;
			}
		}
	}

	if (as().getSolver()->verbosity() >= 5) {
		reportf("STACK: ");
		for (vprop::const_iterator i = getStack().begin(); i < getStack().end(); i++) {
			gprintLit((*i).getLit());
			reportf(" ");
		}
		reportf("\n");

		reportf("Aggregate explanation for ");
		if (ar.isHeadReason()) {
			gprintLit(head);
		} else {
			reportf("(index %d)", index);
			gprintLit((*(as().getWL().begin() + index)).getLit());
		}

		reportf(" is");
		for (int i = 0; i < lits.size(); i++) {
			reportf(" ");
			gprintLit(lits[i]);
		}
		reportf("\n");
	}
}

/*****************
 * MAX AGGREGATE *
 *****************/

MaxFWAgg::MaxFWAgg(paggs agg) :
	FWAgg(agg) {
}

paggs MaxFWAgg::initialize(bool& unsat) {
	if (as().getAgg().size() == 1) { //Simple heuristic to choose for encoding as SAT
		//SAT encoding, not used yet
		bool notunsat = true;
		for (int i = 0; notunsat && i < as().getAgg().size(); i++) {
			/*
			 * For a maximum: if lower,  head <=> conj of negation of all literals with weight higher than bound
			 * 				  if higher, head <=> disj of all literals with weight higher/eq than bound
			 */
			vec<Lit> clause;
			const pagg agg = as().getAgg()[i];
			if (agg->isDefined()) {
				for (vwl::const_reverse_iterator i = as().getWL().rbegin(); i < as().getWL().rend()
							&& (*i).getWeight() >= agg->getBound(); i++) {
					if (agg->isLower() && (*i).getWeight() == agg->getBound()) {
						break;
					}
					if (agg->isLower()) {
						clause.push(~(*i).getLit());
					} else {
						clause.push((*i).getLit());
					}
				}
				notunsat
							= as().getSolver()->getPCSolver()->addRule(
																	agg->isLower() ? LOWERBOUND : UPPERBOUND,
																	agg->getHead(),
																	clause);
			} else {
				clause.push(agg->isLower() ? agg->getHead() : ~agg->getHead());
				for (vwl::const_reverse_iterator i = as().getWL().rbegin(); i < as().getWL().rend()
							&& (*i).getWeight() >= agg->getBound(); i++) {
					if (agg->isLower() && (*i).getWeight() == agg->getBound()) {
						break;
					}
					clause.push((*i).getLit());
				}
				notunsat = as().getSolver()->getPCSolver()->addClause(clause);
				for (vwl::const_reverse_iterator i = as().getWL().rbegin(); notunsat && i < as().getWL().rend()
							&& (*i).getWeight() >= agg->getBound(); i++) {
					if (agg->getBound() && (*i).getWeight() == agg->getBound()) {
						break;
					}
					clause.clear();
					clause.push(agg->isLower() ? ~agg->getHead() : agg->getHead());
					clause.push(~(*i).getLit());
					notunsat = as().getSolver()->getPCSolver()->addClause(clause);
				}
			}
		}
		unsat = !notunsat;
		return NULL;
	} else {
		return FWAgg::initialize(unsat);
	}
}

void MaxFWAgg::addToCertainSet(const WL& l) {
	if (l.getWeight() > getCC()) {
		setCC(l.getWeight());
	}
}

void MaxFWAgg::removeFromPossibleSet(const WL& l) {
	if (l.getWeight() == getCP()) {
		bool found = false;
		for (int i = 0; i < as().getWL().size(); i++) {
			if (truth[i] != l_False) {
				setCP(as().getWL()[i].getWeight());
				found = true;
			}
		}
		if (!found) {
			setCP(as().getESV());
		}
	}
}

/**
 * head is true  && AGG <= B:
 * 		make all literals false with weight larger than bound
 * head is false && A <= AGG:
 * 		make all literals false with weight larger/eq than bound
 */
/**
 * Returns non-owning pointer
 */
rClause MaxFWAgg::propagate(const Agg& agg, bool headtrue) {
	//TODO if(nomoreprops || headprop){ return nullPtrClause; }

	if (false) { //ULTIMATE propagation
		//return maxultimatepropagation(agg, headtrue);
		return NULL;
	} else {
		rClause confl = nullPtrClause;
		if (headtrue && agg.isLower()) {
			for (vwl::const_reverse_iterator i = as().getWL().rbegin(); confl == nullPtrClause && i
						< as().getWL().rend() && agg.getLowerBound() < (*i).getWeight(); i++) {
				//because these propagations are independent of the other set literals, they can also be written as clauses
				confl = as().getSolver()->notifySATsolverOfPropagation(
																	~(*i).getLit(),
																	new AggReason(
																					agg,
																					~(*i).getLit(),
																					HEADONLY));
			}
		} else if (!headtrue && agg.isUpper()) {
			for (vwl::const_reverse_iterator i = as().getWL().rbegin(); confl == nullPtrClause && i
						< as().getWL().rend() && agg.getUpperBound() <= (*i).getWeight(); i++) {
				confl = as().getSolver()->notifySATsolverOfPropagation(
																	~(*i).getLit(),
																	new AggReason(
																					agg,
																					~(*i).getLit(),
																					HEADONLY));
			}
		}
		if (confl == nullPtrClause) {
			confl = propagateAll(agg, headtrue);
		}
		return confl;
	}
}

/*rClause MaxFWAgg::ultimatePropagations(const Agg& agg, bool headtrue){
 if(headtrue){
 vector<WL> wl(getWL());
 WL last = wl[wl.size()-1];
 wl.pop_back();
 for(int i=0; i<getWL().size();i++){
 if(!maxultimatepropagation(wl, agg.getSign(), agg.getBound(), 0, vector<Weight>)){
 //propagate wl.getLit();
 }
 }
 }else{
 //TODO
 return NULL;
 }
 }

 //Return false if all two-valued extensions are false
 bool MaxFWAgg::maxultimatepropagation(const vwl& wl, Bound sign, Weight bound, int index, vector<Weight> weights) {
 if(index==wl.size()){
 return evaluatemax(weights, sign, bound);
 }else{
 vector<Weight> w2(weights);
 w2.push_back(wl[index++].getWeight());
 return maxultimatepropagation(wl, sign, bound, index, weights) || maxultimatepropagation(wl, sign, bound, index, w2);
 }
 }

 bool MaxFWAgg::satisfied(vector<Weight>& weights, Bound sign, Weight bound){
 Weight w = getESV();
 for(int i=0; i<weights.size(); i++){
 if(weights[i]>w){
 w = weights[i];
 }
 }
 return (sign==LOWERBOUND && w<=bound) || (sign==UPPERBOUND && w>=bound);
 }*/

/**
 * If only one value is still possible and the head has already been derived, then this last literal
 * might also be propagated, if the constraint is NOT YET SATISFIED!!!
 *
 * head is true  && A <= AGG: Last literal has to be true
 * head is true  && AGG <= B: No conclusion possible (emptyset is also a solution)
 * head is false && A <= AGG: No conclusion possible (emptyset is also a solution)
 * head is false && AGG <= B: Last literal has to be true
 */
/**
 * Returns non-owning pointer
 */
rClause MaxFWAgg::propagateAll(const Agg& agg, bool headtrue) {
	rClause confl = nullPtrClause;


	//TODO if(nomoreprops || headprop){ return confl; }

	if ((agg.isLower() && headtrue) || (agg.isUpper() && !headtrue)) {
		return confl;
	}

	int pos = -1;
	bool exactlyoneleft = true;
	for (int i = 0; exactlyoneleft && i < as().getWL().size(); i++) {
		const WL& wl = as().getWL()[i];
		if ((agg.isUpper() && headtrue && wl.getWeight() >= agg.getUpperBound()) || (agg.isLower()
					&& !headtrue && wl.getWeight() > agg.getLowerBound())) {
			if (truth[i] == l_Undef) {
				if (pos != -1) {
					exactlyoneleft = false;
				} else {
					pos = i;
				}
			} else if (truth[i] == l_True) {
				exactlyoneleft = false;
			}
		}
	}
	if (exactlyoneleft) {
		//TODO BASEDONCP is not correct enough (ONCPABOVEBOUND)
		confl = as().getSolver()->notifySATsolverOfPropagation(
															as().getWL()[pos].getLit(),
															new AggReason(
																			agg,
																			as().getWL()[pos].getLit(),
																			BASEDONCP));
	}
	return confl;
}

SPFWAgg::SPFWAgg(paggs agg) :
	FWAgg(agg) {
}

void SPFWAgg::addToCertainSet(const WL& l) {
	setCC(this->add(getCC(), l.getWeight()));
}

void SPFWAgg::removeFromPossibleSet(const WL& l) {
	setCP(this->remove(getCP(), l.getWeight()));
}

rClause SPFWAgg::propagate(const Agg& agg, bool headtrue) {
	if (nomoreprops[agg.getIndex()] || headprop[agg.getIndex()]) {
		return nullPtrClause;
	}

	rClause c = nullPtrClause;
	Weight weightbound(0);

	Expl basedon = CPANDCC;
	//determine the lower bound of which weight literals to consider
	if (headtrue) {
		if (agg.isLower()) {
			basedon = BASEDONCC;
			weightbound = remove(agg.getLowerBound(), getCC());
			//+1 because larger and not eq
			if (add(weightbound, getCC()) == agg.getLowerBound()) {
				weightbound += 1;
			}
		} else {
			basedon = BASEDONCP;
			weightbound = remove(getCP(), agg.getUpperBound());
			//+1 because larger and not eq
			if (this->add(weightbound, agg.getUpperBound()) == getCP()) {
				weightbound += 1;
			}
		}
	} else {
		if (agg.isLower()) {
			basedon = BASEDONCP;
			weightbound = remove(getCP(), agg.getLowerBound());
		} else {
			basedon = BASEDONCC;
			weightbound = remove(agg.getUpperBound(), getCC());
		}
	}

#ifdef INTWEIGHT
	if(weightbound == INT_MAX || weightbound == INT_MIN) {
		return c;
	}
#endif

	vwl::const_iterator pos = lower_bound(as().getWL().begin(), as().getWL().end(), weightbound);
	if (pos == as().getWL().end()) {
		return c;
	}

	//find the index of the literal
	int start = 0;
	vwl::const_iterator it = as().getWL().begin();
	while (it != pos) {
		it++;
		start++;
	}

	for (int u = start; c == nullPtrClause && u < as().getWL().size(); u++) {
		if (truth[u] == l_Undef) {//if already propagated as an aggregate, then those best-values have already been adapted
			const Lit& l = as().getWL()[u].getLit();
			if ((agg.isLower() && headtrue) || (agg.isUpper() && !headtrue)) {
				c = as().getSolver()->notifySATsolverOfPropagation(~l, new AggReason(agg, ~l, basedon));
			} else {
				c = as().getSolver()->notifySATsolverOfPropagation(l, new AggReason(agg, l, basedon));
			}
		}
	}
	return c;
}

SumFWAgg::SumFWAgg(paggs agg)
	: SPFWAgg(agg) {

}

paggs SumFWAgg::initialize(bool& unsat) {
	unsat = false;
	if (as().getAgg().size() == 0) {
		return NULL;
	}

	//Calculate the total negative weight to make all weight positive
	vwl wlits2;
	Weight totalneg(0);
	for (vwl::const_iterator i = as().getWL().begin(); i < as().getWL().end(); i++) {
		if ((*i).getWeight() < 0) {
			totalneg -= (*i).getWeight();
		}
	}
	if (totalneg > 0) {
		for (vwl::const_iterator i = as().getWL().begin(); i < as().getWL().end(); i++) {
			wlits2.push_back(WL((*i).getLit(), abs((*i).getWeight())));
		}
		as().getSet()->setWL(wlits2);
		for (vpagg::const_iterator i = as().getAgg().begin(); i < as().getAgg().end(); i++) {
			addToBounds(**i, totalneg);
		}
	}


#ifdef INTWEIGHT
	//Test whether the total sum of the weights is not infinity for intweights
	Weight total(0);
	for(vwl::const_iterator i=as().getWL().begin(); i<as().getWL().end(); i++) {
		if(INT_MAX-total < (*i).getWeight()) {
			throw idpexception("The total sum of weights exceeds max-int, correctness cannot be guaranteed in limited precision.\n");
		}
		total += (*i).getWeight();
	}
#endif

	return FWAgg::initialize(unsat);
}

void SumFWAgg::getMinimExplan(const Agg& agg, vec<Lit>& lits) {
	Weight certainsum = as().getESV();
	Weight possiblesum = as().getBestPossible();

	bool explained = false;
	if ((agg.isLower() && certainsum > agg.getLowerBound()) || (agg.isUpper() && certainsum
				>= agg.getUpperBound()) || (agg.isLower() && possiblesum <= agg.getLowerBound())
				|| (agg.isUpper() && possiblesum < agg.getUpperBound())) {
		explained = true;
	}

	for (vprop::const_iterator i = getStack().begin(); !explained && i < getStack().end(); i++) {
		bool push = false;
		if ((*i).getType() == POS) { //means that the literal in the set became true
			certainsum += (*i).getWeight();

			if (agg.isLower()) {
				push = true;
				if (agg.getLowerBound() < certainsum) {
					explained = true;
				}
			}
		} else if ((*i).getType() == NEG) { //the literal in the set became false
			possiblesum -= (*i).getWeight();

			if (agg.isUpper()) {
				push = true;
				if (possiblesum < agg.getUpperBound()) {
					explained = true;
				}
			}
		}
		if (push) {
			lits.push(~(*i).getLit());
		}
	}

	assert(explained);
}
void SumFWAgg::addToBounds(Agg& agg, const Weight& w) {
	if (agg.isLower()) {
		agg.setLowerBound(add(agg.getLowerBound(), w));
	} else {
		agg.setUpperBound(add(agg.getUpperBound(), w));
	}
}

ProdFWAgg::ProdFWAgg(paggs agg) :
	SPFWAgg(agg) {
}

paggs ProdFWAgg::initialize(bool& unsat) {
	unsat = false;
	if (as().getAgg().size() == 0) {
		return NULL;
	}
#ifdef INTWEIGHT
	//Test whether the total product of the weights is not infinity for intweights
	Weight total(1);
	for(vwl::const_iterator i=as().getWL().begin(); i<as().getWL().end(); i++) {
		if(INT_MAX/total < (*i).getWeight()) {
			throw idpexception("The total product of weights exceeds max-int, correctness cannot be guaranteed in limited precision.\n");
		}
		total *= (*i).getWeight();
	}
#endif

	return FWAgg::initialize(unsat);
}

/************************
 * RECURSIVE AGGREGATES *
 ************************/

bool MaxFWAgg::canJustifyHead(
								const Agg& agg,
								vec<Lit>& jstf,
								vec<Var>& nonjstf,
								vec<int>& currentjust,
								bool real) const {
	AggrType type = agg.getAggComb()->getType();
	bool justified = false;
	const vwl& wl = as().getWL();

	if (agg.isLower()) {
		for (vwl::const_reverse_iterator i = wl.rbegin(); i < wl.rend() && (*i).getWeight()
					> agg.getLowerBound(); i++) {
			if (oppositeIsJustified(*i, currentjust, real, as().getSolver())) {
				jstf.push(~(*i).getLit()); //push negative literal, because it should become false
			} else if (real || currentjust[var((*i).getLit())] != 0) {
				nonjstf.push(var((*i).getLit()));
			}
		}
		if (nonjstf.size() == 0) {
			justified = true;
		}
	} else {
		for (vwl::const_reverse_iterator i = wl.rbegin(); i < wl.rend() && (*i).getWeight()
					>= agg.getUpperBound(); i++) {
			if (isJustified(*i, currentjust, real, as().getSolver())) {
				jstf.push((*i).getLit());
				justified = true;
			} else if (real || currentjust[var((*i).getLit())] != 0) {
				nonjstf.push(var((*i).getLit()));
			}
		}
	}
	if (!justified) {
		jstf.clear();
	}

	return justified;
}

/**
 * AGG <= B: v is justified if one literal below/eq the bound is THAT IS NOT THE HEAD
 * 					if so, change the justification to the literal
 * 					otherwise, add all nonfalse, non-justified, relevant, below the bound literals to the queue
 * A <= AGG: v is justified if the negation of all literals below the bound are. The emptyset is always a solution,
 * 			 so no conclusions have to be drawn from the literals above/eq the bound
 * 					if so, change the justification to the negation of all those below the bound literals
 * 					otherwise, add all nonfalse, non-justified, relevant, below the bound literals to the queue
 */
bool SPFWAgg::canJustifyHead(
								const Agg& agg,
								vec<Lit>& jstf,
								vec<Var>& nonjstf,
								vec<int>& currentjust,
								bool real) const {
	AggrType type = agg.getAggComb()->getType();
	bool justified = false;
	const vwl& wl = as().getWL();

	if (agg.isLower()) {
		Weight bestpossible = as().getBestPossible();
		for (vwl::const_iterator i = wl.begin(); !justified && i < wl.end(); ++i) {
			if (oppositeIsJustified(*i, currentjust, real, as().getSolver())) {
				jstf.push(~(*i).getLit());
				bestpossible = remove(bestpossible, (*i).getWeight());
				if (bestpossible <= agg.getLowerBound()) {
					justified = true;
				}
			} else if (real || currentjust[var((*i).getLit())] != 0) {
				nonjstf.push(var((*i).getLit()));
			}
		}
	} else {
		Weight bestcertain = as().getESV();
		for (vwl::const_iterator i = wl.begin(); !justified && i < wl.end(); ++i) {
			if (isJustified(*i, currentjust, real, as().getSolver())) {
				jstf.push((*i).getLit());
				bestcertain = add(bestcertain, (*i).getWeight());
				if (bestcertain >= agg.getUpperBound()) {
					justified = true;
				}
			} else if (real || currentjust[var((*i).getLit())] != 0) {
				nonjstf.push(var((*i).getLit()));
			}
		}
	}

	if (as().getSolver()->verbosity() >= 4) {
		reportf("Justification checked for ");
		printAgg(agg);

		if (justified) {
			reportf("justification found: ");
			for (int i = 0; i < jstf.size(); i++) {
				gprintLit(jstf[i]);
				reportf(" ");
			}
			reportf("\n");
		} else {
			reportf("no justification found.\n");
		}
	}

	return justified;
}

/**
 * Important: to justify a head, often several body literals have to become FALSE
 * For such literals, they have to be justified if they are NEGATIVE
 *
 * Also, if a literal has to become FALSE, its INVERSION should be added to the justification!
 */
bool Aggrs::oppositeIsJustified(const WL& l, vec<int>& currentjust, bool real, paggsol solver) {
	if (real) {
		return solver->value(l.getLit()) != l_True;
	} else {
		return solver->value(l.getLit()) != l_True && (!sign(l.getLit()) || isJustified(
																						var(l.getLit()),
																						currentjust));
	}
}

bool Aggrs::isJustified(const WL& l, vec<int>& currentjust, bool real, paggsol solver) {
	if (real) {
		return solver->value(l.getLit()) != l_False;
	} else {
		return solver->value(l.getLit()) != l_False && (sign(l.getLit()) || isJustified(
																						var(l.getLit()),
																						currentjust));
	}
}

bool Aggrs::isJustified(Var x, vec<int>& currentjust) {
	return currentjust[x] == 0;
}

///////
//PW Aggregates
///////

PWAgg::PWAgg(paggs agg) :
	Propagator(agg) {
}

CardPWAgg::CardPWAgg(paggs agg) :
	PWAgg(agg) {
}

rClause CardPWAgg::propagate(const Lit& p, const Watch& w) {
	assert(false);
}
;

rClause CardPWAgg::propagate(const Agg& agg) {
	assert(false);
}
;

void CardPWAgg::backtrack(const Agg& agg) {

}

void CardPWAgg::getExplanation(vec<Lit>& lits, const AggReason& ar) const {
	assert(false);
}
;

paggs CardPWAgg::initialize(bool& unsat) {
	SumFWAgg* s = new SumFWAgg(asp());
	for (int i = 0; i < as().getAgg().size(); i++) {
		s->as().addAgg(as().getAgg()[i]);
	}
	as().getRefAgg().clear();
	return s->initialize(unsat);
}
;

bool CardPWAgg::canJustifyHead(
								const Agg& agg,
								vec<Lit>& jstf,
								vec<Var>& nonjstf,
								vec<int>& currentjust,
								bool real) const {
	AggrType type = agg.getAggComb()->getType();
	bool justified = false;
	const vwl& wl = as().getWL();

	if (agg.isLower()) {
		Weight bestpossible = as().getBestPossible();
		for (vwl::const_iterator i = wl.begin(); !justified && i < wl.end(); ++i) {
			if (oppositeIsJustified(*i, currentjust, real, as().getSolver())) {
				jstf.push(~(*i).getLit());
				bestpossible = remove(bestpossible, (*i).getWeight());
				if (bestpossible <= agg.getLowerBound()) {
					justified = true;
				}
			} else if (real || currentjust[var((*i).getLit())] != 0) {
				nonjstf.push(var((*i).getLit()));
			}
		}
	} else {
		Weight bestcertain = as().getESV();
		for (vwl::const_iterator i = wl.begin(); !justified && i < wl.end(); ++i) {
			if (isJustified(*i, currentjust, real, as().getSolver())) {
				jstf.push((*i).getLit());
				bestcertain = add(bestcertain, (*i).getWeight());
				if (bestcertain >= agg.getUpperBound()) {
					justified = true;
				}
			} else if (real || currentjust[var((*i).getLit())] != 0) {
				nonjstf.push(var((*i).getLit()));
			}
		}
	}

	if (as().getSolver()->verbosity() >= 4) {
		reportf("Justification checked for ");
		printAgg(agg);

		if (justified) {
			reportf("justification found: ");
			for (int i = 0; i < jstf.size(); i++) {
				gprintLit(jstf[i]);
				reportf(" ");
			}
			reportf("\n");
		} else {
			reportf("no justification found.\n");
		}
	}

	return justified;
}

///////
// DEBUG
///////

void Aggrs::printAgg(aggs const * const c, bool endl) {
	reportf("%s{", c->getName());
	for (vwl::const_iterator i = c->getWL().begin(); i < c->getWL().end(); ++i) {
		reportf(" ");
		gprintLit((*i).getLit());
		reportf("(%s)", printWeight((*i).getWeight()).c_str());
	}
	if (endl) {
		reportf(" }\n");
	} else {
		reportf(" }");
	}
}

void Aggrs::printAgg(const Agg& ae) {
	gprintLit(ae.getHead());
	paggs set = ae.getAggComb();
	if (ae.isLower()) {
		reportf(" <- ");
	} else {
		reportf(" <- %s <= ", printWeight(ae.getUpperBound()).c_str());
	}
	printAgg(set, false);
	if (ae.isLower()) {
		//reportf(" <= %s. Known values: bestcertain=%s, bestpossible=%s\n", printWeight(ae.getLowerBound()).c_str(), printWeight(set->getCC()).c_str(), printWeight(set->getCP()).c_str());
		reportf(" <= %s.\n", printWeight(ae.getLowerBound()).c_str());
	} else {
		//reportf(". Known values: bestcertain=%s, bestpossible=%s\n", printWeight(set->getCC()).c_str(), printWeight(set->getCP()).c_str());
		reportf(".\n");
	}
}
