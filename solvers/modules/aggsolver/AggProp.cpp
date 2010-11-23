/*
 * AggProp.cpp
 *
 *  Created on: Oct 26, 2010
 *      Author: broes
 */

#include <limits>
#include "solvers/modules/aggsolver/AggProp.hpp"
#include "solvers/modules/aggsolver/AggComb.hpp"
#include "solvers/modules/AggSolver.hpp"
#include "solvers/theorysolvers/PCSolver.hpp"
#include "PbSolver.h"

#include "solvers/modules/aggsolver/FullyWatched.hpp"

#include <assert.h>

using namespace std;
using namespace std::tr1;
using namespace MinisatID;
using namespace MinisatID::Aggrs;

typedef numeric_limits<int> intlim;

shared_ptr<AggProp> AggProp::max = shared_ptr<AggProp> (new MaxProp());
shared_ptr<AggProp> AggProp::sum = shared_ptr<AggProp> (new SumProp());
shared_ptr<AggProp> AggProp::card = shared_ptr<AggProp> (new CardProp());
shared_ptr<AggProp> AggProp::prod = shared_ptr<AggProp> (new ProdProp());

bool MaxProp::isMonotone(const Agg& agg, const WL& l) const {
	return (agg.isLower() && l.getWeight() <= agg.getBound()) || (agg.isUpper());
}

bool SumProp::isMonotone(const Agg& agg, const WL& l) const {
	return (agg.isLower() && l.getWeight() < 0) || (agg.isUpper() && l.getWeight() > 0);
}

bool ProdProp::isMonotone(const Agg& agg, const WL& l) const {
	assert(l.getWeight() == 0 || l.getWeight() >= 1);
	return agg.isUpper();
}

Weight SumProp::add(const Weight& lhs, const Weight& rhs) const {
#ifdef INTWEIGHT
	if (lhs > 0 && rhs > 0 && intlim::max() - lhs < rhs) {
		return intlim::max();
	} else if (lhs < 0 && rhs < 0 && intlim::min() - lhs > rhs) {
		return intlim::min();
	}
#endif
	return lhs + rhs;
}

Weight SumProp::remove(const Weight& lhs, const Weight& rhs) const {
	return lhs - rhs;
}

Weight SumProp::getBestPossible(TypedSet* set) const {
	Weight max = set->getESV();
	for (vwl::const_iterator j = set->getWL().begin(); j < set->getWL().end(); j++) {
		max = this->add(max, (*j).getWeight());
	}
	return max;
}

Weight SumProp::getCombinedWeight(const Weight& one, const Weight& two) const {
	return this->add(one, two);
}

WL SumProp::handleOccurenceOfBothSigns(const WL& one, const WL& two, TypedSet* set) const {
	if (one.getWeight() < two.getWeight()) {
		set->setESV(set->getESV() + one.getWeight());
		return WL(two.getLit(), this->remove(two.getWeight(), one.getWeight()));
	} else {
		set->setESV(set->getESV() + two.getWeight());
		return WL(one.getLit(), this->remove(one.getWeight(), two.getWeight()));
	}
}

///////
// CARD Prop
///////

Weight CardProp::getBestPossible(TypedSet* set) const {
	Weight max = set->getESV();
	for (vwl::const_iterator j = set->getWL().begin(); j < set->getWL().end(); j++) {
		max = this->add(max, (*j).getWeight());
	}
	return max;
}

Weight CardProp::add(const Weight& lhs, const Weight& rhs) const {
#ifdef INTWEIGHT
	if (lhs > 0 && rhs > 0 && intlim::max() - lhs < rhs) {
		return intlim::max();
	} else if (lhs < 0 && rhs < 0 && intlim::min() - lhs > rhs) {
		return intlim::min();
	}
#endif
	return lhs + rhs;
}

Weight CardProp::remove(const Weight& lhs, const Weight& rhs) const {
	return lhs - rhs;
}

Weight CardProp::getCombinedWeight(const Weight& one, const Weight& two) const {
	return this->add(one, two);
}

WL CardProp::handleOccurenceOfBothSigns(const WL& one, const WL& two, TypedSet* set) const {
	if (one.getWeight() < two.getWeight()) {
		set->setESV(set->getESV() + one.getWeight());
		return WL(two.getLit(), this->remove(two.getWeight(), one.getWeight()));
	} else {
		set->setESV(set->getESV() + two.getWeight());
		return WL(one.getLit(), this->remove(one.getWeight(), two.getWeight()));
	}
}

///////
// MAX Prop
///////

Weight MaxProp::getBestPossible(TypedSet* set) const {
	return set->getWL().back().getWeight();
}

Weight MaxProp::getCombinedWeight(const Weight& first, const Weight& second) const {
	return first > second ? first : second;
}

WL MaxProp::handleOccurenceOfBothSigns(const WL& one, const WL& two, TypedSet* set) const {
	if (one.getWeight() > two.getWeight()) {
		if (set->getESV() < two.getWeight()) {
			set->setESV(two.getWeight());
		}
		return one;
	} else {
		if (set->getESV() < one.getWeight()) {
			set->setESV(one.getWeight());
		}
		return two;
	}
}

///////
// PROD Prop
///////

Weight ProdProp::getBestPossible(TypedSet* set) const {
	Weight max = set->getESV();
	for(vwl::const_iterator j = set->getWL().begin(); j<set->getWL().end(); j++){
		max = this->add(max, (*j).getWeight());
	}
	return max;
}

Weight ProdProp::add(const Weight& lhs, const Weight& rhs) const {
	assert(lhs!=0 && rhs!=0);
#ifdef INTWEIGHT
	bool sign = false;
	Weight l = lhs, r = rhs;
	if(l<0){
		l = -l;
		sign = true;
	}
	if(r<0){
		r = -r;
		sign = !sign;
	}
	if(intlim::max()/l < r){
		return sign ? intlim::min() : intlim::max();
	}
#endif
	return lhs * rhs;
}

Weight ProdProp::remove(const Weight& lhs, const Weight& rhs) const {
	Weight w = 0;
	if (rhs != 0) {
		w = lhs / rhs;
		if (w == 1 && lhs > rhs) {
			w = 2;
		}
	}

	return w;
}

Weight ProdProp::getCombinedWeight(const Weight& one, const Weight& two) const {
	return this->add(one, two);
}

WL ProdProp::handleOccurenceOfBothSigns(const WL& one, const WL& two, TypedSet* set) const {
	//NOTE: om dit toe te laten, ofwel bij elke operatie op en literal al zijn voorkomens overlopen
	//ofwel aggregaten voor doubles ondersteunen (het eerste is eigenlijk de beste oplossing)
	//Mogelijke eenvoudige implementatie: weigts bijhouden als doubles (en al de rest als ints)
	report("Product aggregates in which both the literal and its negation occur "
			"are currently not supported. Replace ");
	gprintLit(one.getLit());
	report("or ");
	gprintLit(two.getLit());
	report("by a tseitin.\n");
	throw idpexception("Atoms in product aggregates have to be unique.\n");
}

///////
// TypedSet
///////

Propagator*	MaxProp::createPropagator(TypedSet* set, bool pw) const{
	return new MaxFWAgg(set);
}

Propagator*	SumProp::createPropagator(TypedSet* set, bool pw) const{
	return new SumFWAgg(set);
}

Propagator*	ProdProp::createPropagator(TypedSet* set, bool pw) const{
	return new ProdFWAgg(set);
}



int Agg::getSetID() const	{
	return set==NULL?-1:set->getSetID();
}


void TypedSet::addAgg(Agg* aggr){
	assert(aggr!=NULL);
	aggregates.push_back(aggr);
	aggr->setTypedSet(this);
	aggr->setIndex(aggregates.size()-1);
}

void TypedSet::replaceAgg(const vpagg& repl){
	for(vpagg::const_iterator i=aggregates.begin(); i<aggregates.end(); i++){
		(*i)->setTypedSet(NULL);
		(*i)->setIndex(-1);
	}
	aggregates.clear();
	for(vector<Agg*>::const_iterator i=repl.begin(); i<repl.end(); i++){
		addAgg((*i));
	}
}

/*
 * Initialize the datastructures. If it's neither sat nor unsat and it is defined, notify the pcsolver of this
 */
void TypedSet::initialize(bool& unsat, bool& sat) {
	setProp(getType().createPropagator(this, this->getSolver()->getPCSolver()->modes().pw));
	prop->initialize(unsat, sat);

	if (!sat && !unsat) {
		for (vsize i = 0; i < getAgg().size(); i++) {
			if (getAgg()[i]->isDefined()) {
				getSolver()->notifyDefinedHead(var(getAgg()[i]->getHead()));
			}
		}
	}
}

// Final initialization call!
void Propagator::initialize(bool& unsat, bool& sat) {
	for (vsize i = 0; i < getSet().getAgg().size(); i++) {
		getSolver()->setHeadWatch(var(getSet().getAgg()[i]->getHead()), getSet().getAgg()[i]);
	}
}

///////
// HELP METHODS
///////

AggSolver* Propagator::getSolver() const {
	return getSetp()->getSolver();
}

rClause Propagator::notifySolver(AggReason* reason) {
	return getSolver()->notifySolver(reason);
}

lbool Propagator::value(const Lit& l) const {
	return getSolver()->value(l);
}

///////
// TRANSFORMATIONS
///////

bool Aggrs::compareWLByLits(const WL& one, const WL& two) {
	return var(one.getLit()) < var(two.getLit());
}

bool Aggrs::compareWLByWeights(const WL& one, const WL& two) {
	return one.getWeight() < two.getWeight();
}

//@pre: has been split
bool Aggrs::transformSetReduction(TypedSet* set, vps& sets) {
	vwl oldset = set->getWL();
	vwl newset;

	//Sort all wlits according to the integer representation of their literal (to get all literals next to each other)
	std::sort(oldset.begin(), oldset.end(), compareWLByLits);

	int indexinnew = 0;
	newset.push_back(oldset[indexinnew]);

	bool setisreduced = false;
	for (vwl::size_type i = 1; i < oldset.size(); i++) {
		WL oldl = newset[indexinnew];
		WL newl = oldset[i];
		if (var(oldl.getLit()) == var(newl.getLit())) { //same variable
			setisreduced = true;
			if (oldl.getLit() == newl.getLit()) { //same literal, keep combined weight
				Weight w = set->getType().getCombinedWeight(newl.getWeight(), oldl.getWeight());
				newset[indexinnew] = WL(oldl.getLit(), w);
			} else { //opposite signs
				WL wl = set->getType().handleOccurenceOfBothSigns(oldl, newl, set);
				newset[indexinnew] = WL(wl.getLit(), wl.getWeight());
			}
		} else {
			newset.push_back(newl);
			indexinnew++;
		}
	}

	vwl newset2;
	bool canbecard = true;
	for (vwl::size_type i = 0; i < newset.size(); i++) {
		if (!set->getType().isNeutralElement(newset[i].getWeight())) {
			newset2.push_back(newset[i]);
			if (newset[i].getWeight() != 1) {
				canbecard = false;
			}
		} else {
			setisreduced = true;
		}
	}

	if (setisreduced) {
		set->setWL(newset2);
	}

	//Correct the aggregate types!
	if (canbecard) {
		if(set->getType().getType()==SUM){
			set->setType(AggProp::getCard());
			for (vpagg::const_iterator i = set->getAgg().begin(); i < set->getAgg().end(); i++) {
				if ((*i)->getType() == SUM) {
					(*i)->setType(CARD);
				}
			}
		}
	} else {
		if(set->getType().getType()==CARD){
			set->setType(AggProp::getSum());
			for (vpagg::const_iterator i = set->getAgg().begin(); i < set->getAgg().end(); i++) {
				if ((*i)->getType() == CARD) {
					(*i)->setType(SUM);
				}
			}
		}
	}

	return true;
}

//FIXME increase performance by treating transformation on a set to set basis?

bool Aggrs::transformOneToOneSetToAggMapping(TypedSet* set, vps& sets) {
	vpagg aggs = set->getAgg();

	vpagg newaggs;
	newaggs.push_back(aggs[0]);
	set->replaceAgg(newaggs);

	for (vpagg::const_iterator i = ++aggs.begin(); i < aggs.end(); i++) {
		TypedSet* newset = new TypedSet(set->getSolver(), set->getSetID());
		newset->addAgg(*i);
		newset->setWL(set->getWL());
		sets.push_back(newset);
	}

	return true;
}

bool Aggrs::transformOneToOneSetToSignMapping(TypedSet* setone, vps& sets) {
	vpagg aggs = setone->getAgg();

	vpagg newaggs;
	newaggs.push_back(aggs[0]);
	setone->replaceAgg(newaggs);

	TypedSet* settwo = new TypedSet(setone->getSolver(), setone->getSetID());
	settwo->setWL(setone->getWL());

	for (vpagg::const_iterator i = ++aggs.begin(); i < aggs.end(); i++) {
		if ((*i)->getSign() == setone->getAgg()[0]->getSign()) {
			setone->addAgg(*i);
		} else {
			settwo->addAgg(*i);
		}
	}

	if (settwo->getAgg().size() > 0) {
		sets.push_back(settwo);
	} else {
		delete settwo;
	}
	return true;
}

//@pre: at least one aggregate present
bool Aggrs::transformTypePartition(TypedSet* set, vps& sets) {
	assert(set->getAgg().size() > 0);
	//Partition the aggregates according to their type
	map<AggType, vpagg> partaggs;
	for (vpagg::const_iterator i = set->getAgg().begin(); i < set->getAgg().end(); i++) {
		partaggs[(*i)->getType()].push_back(*i);
	}

	map<AggType, vpagg>::const_iterator i = partaggs.begin();
	set->replaceAgg((*i).second);
	i++;
	for (; i != partaggs.end(); i++) {
		TypedSet* newset = new TypedSet(set->getSolver(), set->getSetID());
		newset->replaceAgg((*i).second);
		newset->setWL(set->getWL());
		sets.push_back(newset);
	}
	return true;
}

//@pre Has to be split
bool Aggrs::transformVerifyWeights(TypedSet* set, vps& sets) {
	if (set->getAgg()[0]->getType() == PROD) {
		for (vsize i = 0; i < set->getWL().size(); i++) {
			if (set->getWL()[i] < 1) { //Exception if product contains negative/zero weights
				char s[200];
				sprintf(s, "Error: Set nr. %d contains a 0 (zero) or negative weight %s, which cannot "
					"be used in combination with a product aggregate\n", set->getSetID(), printWeight(
						set->getWL()[i]).c_str());
				throw idpexception(s);
			}
		}
	}
	return true;
}

//@pre Has to be split
//Adds the type objects and correct esv to the sets
bool Aggrs::transformAddTypes(TypedSet* set, vps& sets) {
	switch (set->getAgg()[0]->getType()) {
		case MAX:
			set->setType(AggProp::getMax());
			set->setESV(intlim::min());
			break;
		case SUM:
			set->setType(AggProp::getSum());
			set->setESV(0);
			break;
		case CARD:
			set->setType(AggProp::getCard());
			set->setESV(0);
			break;
		case PROD:
			set->setType(AggProp::getProd());
			set->setESV(1);
			break;
		default:
			assert(false);
	}
	return true;
}

bool Aggrs::transformMinToMax(TypedSet* set, vps& sets) {
	if (set->getAgg()[0]->getType() == MIN) {
		//Transform Min into Max set: invert all weights
		vwl wl;
		for (vsize i = 0; i < set->getWL().size(); i++) {
			wl.push_back(WL(set->getWL()[i], -set->getWL()[i]));
		}
		set->setWL(wl);

		//Invert the bound of all the aggregates involved
		for (vpagg::const_iterator i = set->getAgg().begin(); i < set->getAgg().end(); i++) {
			(*i)->setSign((*i)->getSign() == LB ? UB : LB);
			(*i)->setBound(-(*i)->getBound());
		}
		set->getAgg()[0]->setType(MAX);
	}
	return true;
}

/**
 * Rewrites cards as sets of clauses iff:
 * 	bound-esv == 0 && upper => head is always true
 * 	bound-esv == 1 && upper => write out equivalence if not too large
 * 								if large, only write out if head already true
 * 	TODO others?
 */
bool Aggrs::transformCardGeqOneToEquiv(TypedSet* set, vps& sets){
	bool unsat = false;
	if (set->getAgg()[0]->getType() == CARD) {
		vpagg remaggs;
		for (vpagg::const_iterator i = set->getAgg().begin(); !unsat && i < set->getAgg().end(); i++) {
			if((*i)->getBound()-set->getESV()==0 && (*i)->isUpper()){
				vec<Lit> lits;
				bool unsat = false;
				if ((*i)->getSem() == DEF) {
					unsat = !set->getSolver()->getPCSolver()->addRule(true, (*i)->getHead(), lits);
				}else{
					lits.push((*i)->getHead());
					unsat = !set->getSolver()->getPCSolver()->addClause(lits);
				}
			} else if((*i)->getBound()-set->getESV()==1 && (*i)->isUpper()){
				vec<Lit> right;
				for (vsize j = 0; j < set->getWL().size(); j++) {
					right.push(set->getWL()[j]);
				}
				if ((*i)->getSem() == DEF) {
					unsat = !set->getSolver()->getPCSolver()->addRule(false, (*i)->getHead(), right);
				} else{
					unsat = !set->getSolver()->getPCSolver()->addEquivalence((*i)->getHead(), right, false);
				}
			} else{
				remaggs.push_back(*i);
			}
		}
		set->replaceAgg(remaggs);
	}
	return !unsat;
}

//Temporary structure to create pseudo booleans
struct PBAgg {
	MiniSatPP::vec<MiniSatPP::Lit> literals;
	MiniSatPP::vec<MiniSatPP::Int> weights;
	Weight bound;
	int sign;
};

bool Aggrs::transformSumsToCNF(vps& sets, MinisatID::PCSolver* pcsolver) {
	int sumaggs = 0;
	int maxvar = 1;
	vector<PBAgg*> pbaggs;
	for (vps::const_iterator i = sets.begin(); i != sets.end(); i++) {
		vpagg remaining;
		for (vsize j = 0; j < (*i)->getAgg().size(); j++) {
			Agg* agg = (*i)->getAgg()[j];
			if (!agg->isOptim() && (agg->getType() == SUM || agg->getType() == CARD) && !agg->getSem() == DEF) {
				PBAgg* ppbaggeq = new PBAgg();
				PBAgg* ppbaggineq = new PBAgg();
				pbaggs.push_back(ppbaggeq);
				pbaggs.push_back(ppbaggineq);
				PBAgg& pbaggeq = *ppbaggeq;
				PBAgg& pbaggineq = *ppbaggineq;
				if (agg->getSign() == LB) {
					pbaggeq.sign = -1;
					pbaggineq.sign = 2;
				} else {
					pbaggeq.sign = 1;
					pbaggineq.sign = -2;
				}
				pbaggeq.bound = agg->getBound();
				pbaggineq.bound = agg->getBound();
				Weight min = 0, max = 0;
				for (vwl::const_iterator k = (*i)->getWL().begin(); k < (*i)->getWL().end(); k++) {
					pbaggeq.literals.push(MiniSatPP::Lit(var((*k).getLit()), sign((*k).getLit())));
					pbaggineq.literals.push(MiniSatPP::Lit(var((*k).getLit()), sign((*k).getLit())));
					if (var((*k).getLit()) > maxvar) {
						maxvar = var((*k).getLit());
					}
					if ((*k).getWeight() < 0) {
						min += (*k).getWeight();
					} else {
						max += (*k).getWeight();
					}
					pbaggeq.weights.push(MiniSatPP::Int((int) ((*k).getWeight())));
					pbaggineq.weights.push(MiniSatPP::Int((int) ((*k).getWeight())));
				}
				if (var(agg->getHead()) > maxvar) {
					maxvar = var(agg->getHead());
				}
				pbaggeq.literals.push(MiniSatPP::Lit(var(agg->getHead()), true));
				pbaggineq.literals.push(MiniSatPP::Lit(var(agg->getHead()), false));
				Weight eqval, ineqval;
				if (agg->getSign() == LB) {
					eqval = -abs(agg->getBound()) - abs(max) - 1;
					ineqval = abs(agg->getBound()) + abs(min) + 1;
				} else {
					eqval = abs(agg->getBound()) + abs(min) + 1;
					ineqval = -abs(agg->getBound()) - abs(max) - 1;
				}
				pbaggeq.weights.push(MiniSatPP::Int(eqval));
				pbaggineq.weights.push(MiniSatPP::Int(ineqval));
			} else {
				remaining.push_back(agg);
			}
		}
		(*i)->replaceAgg(remaining);
	}

	MiniSatPP::PbSolver* pbsolver = new MiniSatPP::PbSolver();
	MiniSatPP::opt_verbosity = pcsolver->modes().verbosity;
	MiniSatPP::opt_abstract = true; //Should be true
	MiniSatPP::opt_tare = true; //Experimentally set to true
	MiniSatPP::opt_primes_file = pcsolver->modes().primesfile;
	MiniSatPP::opt_convert_weak = false;
	MiniSatPP::opt_convert = MiniSatPP::ct_Mixed;
	pbsolver->allocConstrs(maxvar, sumaggs);

	bool unsat = false;
	for (vector<PBAgg*>::const_iterator i = pbaggs.begin(); !unsat && i < pbaggs.end(); i++) {
		unsat = !pbsolver->addConstr((*i)->literals, (*i)->weights, (*i)->bound, (*i)->sign, false);
	}
	deleteList<PBAgg> (pbaggs);

	if (unsat) {
		delete pbsolver;
		return false;
	}

	//get CNF out of the pseudoboolean matrix
	vector<vector<MiniSatPP::Lit> > pbencodings;
	unsat = !pbsolver->toCNF(pbencodings);
	delete pbsolver;
	if (unsat) {
		return false;
	}

	//Any literal that is larger than maxvar will have been newly introduced, so should be mapped to nVars()+lit
	//add the CNF to the solver
	int maxnumber = pcsolver->nVars();
	for (vector<vector<MiniSatPP::Lit> >::const_iterator i = pbencodings.begin(); i < pbencodings.end(); i++) {
		vec<Lit> lits;
		for (vector<MiniSatPP::Lit>::const_iterator j = (*i).begin(); j < (*i).end(); j++) {
			Var v = MiniSatPP::var(*j) + (MiniSatPP::var(*j) > maxvar ? maxnumber - maxvar : 0);
			lits.push(mkLit(v, MiniSatPP::sign(*j)));
		}
		pcsolver->addClause(lits);
	}

	return true;
}

/************************
 * RECURSIVE AGGREGATES *
 ************************/

bool MaxProp::canJustifyHead(const Agg& agg, vec<Lit>& jstf, vec<Var>& nonjstf, vec<int>& currentjust, bool real) const {
	TypedSet* set = agg.getSet();
	bool justified = false;
	const vwl& wl = set->getWL();

	if (agg.isLower()) {
		for (vwl::const_reverse_iterator i = wl.rbegin(); i < wl.rend() && (*i).getWeight() > agg.getBound(); i++) {
			if (oppositeIsJustified(*i, currentjust, real, set->getSolver())) {
				jstf.push(~(*i).getLit()); //push negative literal, because it should become false
			} else if (real || currentjust[var((*i).getLit())] != 0) {
				nonjstf.push(var((*i).getLit()));
			}
		}
		if (nonjstf.size() == 0) {
			justified = true;
		}
	} else {
		for (vwl::const_reverse_iterator i = wl.rbegin(); i < wl.rend() && (*i).getWeight() >= agg.getBound(); i++) {
			if (isJustified(*i, currentjust, real, set->getSolver())) {
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
bool SPProp::canJustifyHead(const Agg& agg, vec<Lit>& jstf, vec<Var>& nonjstf, vec<int>& currentjust, bool real) const {
	TypedSet* set = agg.getSet();
	const AggProp& type = agg.getSet()->getType();
	bool justified = false;
	const vwl& wl = set->getWL();

	if (agg.isLower()) {
		Weight bestpossible = type.getBestPossible(set);
		for (vwl::const_iterator i = wl.begin(); !justified && i < wl.end(); ++i) {
			if (oppositeIsJustified(*i, currentjust, real, set->getSolver())) {
				jstf.push(~(*i).getLit());
				bestpossible = type.remove(bestpossible, (*i).getWeight());
				if (bestpossible <= agg.getBound()) {
					justified = true;
				}
			} else if (real || currentjust[var((*i).getLit())] != 0) {
				nonjstf.push(var((*i).getLit()));
			}
		}
	} else {
		Weight bestcertain = set->getESV();
		for (vwl::const_iterator i = wl.begin(); !justified && i < wl.end(); ++i) {
			if (isJustified(*i, currentjust, real, set->getSolver())) {
				jstf.push((*i).getLit());
				bestcertain = type.add(bestcertain, (*i).getWeight());
				if (bestcertain >= agg.getBound()) {
					justified = true;
				}
			} else if (real || currentjust[var((*i).getLit())] != 0) {
				nonjstf.push(var((*i).getLit()));
			}
		}
	}

	if (set->getSolver()->verbosity() >= 4) {
		report("Justification checked for ");
		printAgg(agg, true);

		if (justified) {
			report("justification found: ");
			for (int i = 0; i < jstf.size(); i++) {
				gprintLit(jstf[i]);
				report(" ");
			}
			report("\n");
		} else {
			report("no justification found.\n");
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
