#include "solvers/aggsolver/AggComb.hpp"

#include "solvers/aggsolver/AggSolver.hpp"
#include "solvers/aggsolver/FullyWatched.hpp"
#include "solvers/aggsolver/PartiallyWatched.hpp"

#include "solvers/pcsolver/PCSolver.hpp"

#include <algorithm>

#include <stdint.h>
#include <inttypes.h>
#include <limits.h>

using namespace Aggrs;

WL Watch::getWL() const {
	return agg->getWL()[index];
}

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
	agg->setProp(this);
}

MaxCalc::MaxCalc(const paggsol& solver, const vwl& wl):
	CalcAgg(solver, wl){
	//FIXME moet eigenlijk een voorstelling van -infinity zijn
	//ik had eerst: |minimum van de set| -1, maar de bound zelf kan NOG lager liggen, dus dan is het fout
	setESV(Weight(INT_MIN));
	assert(getESV() <= INT_MIN);

	new MaxFWAgg(this);
}

SPCalc::SPCalc(const paggsol& solver, const vwl& wl):
			CalcAgg(solver, wl){
}

SumCalc::SumCalc(const paggsol& solver, const vwl& wl):
			SPCalc(solver, wl){
	setESV(0);
	new SumFWAgg(this);
}

ProdCalc::ProdCalc(const paggsol& solver, const vwl& wl):
			SPCalc(solver, wl){
	setESV(1);
	new ProdFWAgg(this);
}

CardCalc::CardCalc(const paggsol& solver, const vwl& wl):
			SPCalc(solver, wl){
	setESV(0);
	new CardPWAgg(this);
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

void CalcAgg::initialize(bool& unsat, bool& sat) {
	prop->initialize(unsat, sat);
}

// Final initialization call!
void Propagator::initialize(bool& unsat, bool& sat) {
	for (int i = 0; i < as().getAgg().size(); i++) {
		as().getSolver()->setHeadWatch(var(as().getAgg()[i]->getHead()), as().getAgg()[i]);
	}
}

lbool Propagator::value(Lit l) const {
	return as().getSolver()->value(l);
}

/************************
 * RECURSIVE AGGREGATES *
 ************************/

bool MaxCalc::canJustifyHead(
								const Agg& agg,
								vec<Lit>& jstf,
								vec<Var>& nonjstf,
								vec<int>& currentjust,
								bool real) const {
	AggrType type = agg.getAggComb()->getType();
	bool justified = false;
	const vwl& wl = getWL();

	if (agg.isLower()) {
		for (vwl::const_reverse_iterator i = wl.rbegin(); i < wl.rend() && (*i).getWeight()	> agg.getLowerBound(); i++) {
			if (oppositeIsJustified(*i, currentjust, real, getSolver())) {
				jstf.push(~(*i).getLit()); //push negative literal, because it should become false
			} else if (real || currentjust[var((*i).getLit())] != 0) {
				nonjstf.push(var((*i).getLit()));
			}
		}
		if (nonjstf.size() == 0) {
			justified = true;
		}
	} else {
		for (vwl::const_reverse_iterator i = wl.rbegin(); i < wl.rend() && (*i).getWeight()	>= agg.getUpperBound(); i++) {
			if (isJustified(*i, currentjust, real, getSolver())) {
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
bool SPCalc::canJustifyHead(
								const Agg& agg,
								vec<Lit>& jstf,
								vec<Var>& nonjstf,
								vec<int>& currentjust,
								bool real) const {
	AggrType type = agg.getAggComb()->getType();
	bool justified = false;
	const vwl& wl = getWL();

	if (agg.isLower()) {
		Weight bestpossible = getBestPossible();
		for (vwl::const_iterator i = wl.begin(); !justified && i < wl.end(); ++i) {
			if (oppositeIsJustified(*i, currentjust, real, getSolver())) {
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
		Weight bestcertain = getESV();
		for (vwl::const_iterator i = wl.begin(); !justified && i < wl.end(); ++i) {
			if (isJustified(*i, currentjust, real, getSolver())) {
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

	if (getSolver()->verbosity() >= 4) {
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

/*bool SPAgg::canJustifyHead(vec<Lit>& jstf, vec<Var>& nonjstf, vec<int>& currentjust, bool real) const {
	//OTHER IMPLEMENTATION (probably buggy)
	pSet s = getSet();

	Weight current = 0;
	if(isLower()){
		current = s->getBestPossible();
	}else{
		current = s->getEmptySetValue();
	}

	bool justified = false;
	if(aggValueImpliesHead(current)){
		justified = true;
	}

	for (lwlv::const_iterator i = s->getWLBegin(); !justified && i < s->getWLEnd(); ++i) {
		if(isMonotone(*i) && s->isJustified(*i, currentjust, real)){
			if(isLower()){
				jstf.push(~(*i).getLit());
				current = this->remove(current, (*i).getWeight());
			}else{
				//if(s->isJustified(*i, currentjust, real)){
				jstf.push((*i).getLit());
				current = this->add(current, (*i).getWeight());
			}

			if (aggValueImpliesHead(current)){
				justified = true;
			}
		}else if(real ||currentjust[var((*i).getLit())]!=0){
			nonjstf.push(var((*i).getLit()));
		}
	}

	if (!justified) {
		jstf.clear();
	}

	if(s->getSolver()->getPCSolver()->modes().verbosity >=4){
		reportf("Justification checked for ");
		printAggrExpr(this);

		if(justified){
			reportf("justification found: ");
			for(int i=0; i<jstf.size(); i++){
				gprintLit(jstf[i]); reportf(" ");
			}
			reportf("\n");
		}else{
			reportf("no justification found.\n");
		}
	}

	return justified;
}*/

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
