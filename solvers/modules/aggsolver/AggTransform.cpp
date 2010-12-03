#include "AggTransform.hpp"

#include <limits>

#include "modules/aggsolver/AggProp.hpp"
#include "modules/aggsolver/AggPrint.hpp"
#include "modules/aggsolver/AggUtils.hpp"
#include "modules/AggSolver.hpp"
#include "theorysolvers/PCSolver.hpp"

#include "PbSolver.h"

using namespace std;
using namespace tr1;
using namespace MinisatID;
using namespace Aggrs;

typedef numeric_limits<int> intlim;

///////
// TRANSFORMATIONS
///////

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
					"be used in combination with a product aggregate\n", set->getSetID(), toString(
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
			wl.push_back(WL(set->getWL()[i], -set->getWL()[i].getWeight()));
		}
		set->setWL(wl);

		//Invert the bound of all the aggregates involved
		for (vpagg::const_iterator i = set->getAgg().begin(); i < set->getAgg().end(); i++) {
			Weight bound = -(*i)->getBound();
			AggSign sign = (*i)->getSign()==AGGSIGN_LB?AGGSIGN_UB:AGGSIGN_LB;
			(*i)->setBound(AggBound(sign, bound));
		}
		set->getAgg()[0]->setType(MAX);
	}
	return true;
}

//After type setting and transforming to max
bool Aggrs::transformMaxToSAT(TypedSet* set, vps& sets){
	//Simple heuristic to choose for encoding as SAT
	if (set->getType().getType()!=MAX || set->getAgg().size() != 1) {
		return true;
	}
	bool notunsat = true;
	assert( set->getAgg().size()==1);
	/*
	 * For a maximum: if lower,  head <=> conj of negation of all literals with weight higher than bound
	 * 				  if higher, head <=> disj of all literals with weight higher/eq than bound
	 */
	vec<Lit> clause;

	const Agg& agg = *set->getAgg()[0];
	bool ub = agg.hasUB();
	const Weight& bound = agg.getBound();
	if (agg.isDefined()) {
		for (vwl::const_reverse_iterator i = set->getWL().rbegin(); i < set->getWL().rend()
					&& (*i).getWeight() >= bound; i++) {
			if (ub && (*i).getWeight() == bound) {
				break;
			}
			if (ub) {
				clause.push(~(*i).getLit());
			} else {
				clause.push((*i).getLit());
			}
		}
		notunsat = set->getSolver()->getPCSolver()->addRule(ub,agg.getHead(),clause);
	} else {
		clause.push(ub? agg.getHead():~agg.getHead());
		for (vwl::const_reverse_iterator i = set->getWL().rbegin(); i < set->getWL().rend()
					&& (*i).getWeight() >= bound; i++) {
			if (ub && (*i).getWeight() == bound) {
				break;
			}
			clause.push((*i).getLit());
		}
		notunsat = set->getSolver()->getPCSolver()->addClause(clause);
		for (vwl::const_reverse_iterator i = set->getWL().rbegin(); notunsat && i < set->getWL().rend()
					&& (*i).getWeight() >= bound; i++) {
			if (ub && (*i).getWeight() == bound) {
				break;
			}
			clause.clear();
			clause.push(ub?~agg.getHead():agg.getHead());
			clause.push(~(*i).getLit());
			notunsat = set->getSolver()->getPCSolver()->addClause(clause);
		}
	}
	set->replaceAgg(vector<Agg*>());
	return notunsat;
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
			const Agg& agg = *(*i);
			if(agg.hasLB()){
				const Weight& bound = agg.getBound();
				if(bound-set->getESV()==0){
					lbool headvalue = set->getSolver()->value(agg.getHead());
					if(headvalue==l_False){
						unsat = true;
					}else{
						if (agg.getSem() == DEF) {
							vec<Lit> lits;
							unsat = unsat || !set->getSolver()->getPCSolver()->addRule(true, agg.getHead(), lits);
						}else{
							if(headvalue==l_Undef){
								if(set->getSolver()->notifySolver(new AggReason(agg, HEADONLY, agg.getHead(), 0, true))!=nullPtrClause){
									unsat = true;
								}
							}
						}
					}
				} else if(bound-set->getESV()==1){
					vec<Lit> right;
					for (vsize j = 0; j < set->getWL().size(); j++) {
						right.push(set->getWL()[j]);
					}
					if (agg.getSem() == DEF) {
						unsat = !set->getSolver()->getPCSolver()->addRule(false, agg.getHead(), right);
					} else{
						unsat = !set->getSolver()->getPCSolver()->addEquivalence(agg.getHead(), right, false);
					}
				}else{
					remaggs.push_back(*i);
				}
			}else{
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

//TODO allow complete translation into sat? => double bounds, defined aggregates, optimization
bool Aggrs::transformSumsToCNF(vps& sets, PCSolver* pcsolver) {
	int sumaggs = 0;
	int maxvar = 1;
	vector<PBAgg*> pbaggs;
	for (vps::const_iterator i = sets.begin(); i != sets.end(); i++) {
		vpagg remaining;
		for (vsize j = 0; j < (*i)->getAgg().size(); j++) {
			Agg* agg = (*i)->getAgg()[j];

			if(agg->isOptim()
					|| (agg->getType()!=SUM && agg->getType()!=CARD)
					|| agg->getSem() == DEF){
				remaining.push_back(agg);
				continue;
			}

			PBAgg* ppbaggeq = new PBAgg();
			PBAgg* ppbaggineq = new PBAgg();
			pbaggs.push_back(ppbaggeq);
			pbaggs.push_back(ppbaggineq);
			PBAgg& pbaggeq = *ppbaggeq;
			PBAgg& pbaggineq = *ppbaggineq;
			Weight bound = agg->getBound();
			if (agg->hasUB()) {
				pbaggeq.sign = -1;
				pbaggineq.sign = 2;
			} else {
				pbaggeq.sign = 1;
				pbaggineq.sign = -2;
			}
			pbaggeq.bound = bound;
			pbaggineq.bound = bound;
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
				pbaggeq.weights.push((*k).getWeight());
				pbaggineq.weights.push((*k).getWeight());
			}
			if (var(agg->getHead()) > maxvar) {
				maxvar = var(agg->getHead());
			}
			pbaggeq.literals.push(MiniSatPP::Lit(var(agg->getHead()), true));
			pbaggineq.literals.push(MiniSatPP::Lit(var(agg->getHead()), false));
			Weight eqval, ineqval;
			if (agg->hasUB()) {
				eqval = -abs(bound) - abs(max) - 1;
				ineqval = abs(bound) + abs(min) + 1;
			} else {
				eqval = abs(bound) + abs(min) + 1;
				ineqval = -abs(bound) - abs(max) - 1;
			}
			pbaggeq.weights.push(eqval);
			pbaggineq.weights.push(ineqval);
		}
		(*i)->replaceAgg(remaining);
	}

	MiniSatPP::PbSolver* pbsolver = new MiniSatPP::PbSolver();
	MiniSatPP::opt_verbosity = pcsolver->verbosity()-1; //Gives a bit too much output on 1
	MiniSatPP::opt_abstract = true; //Should be true
	MiniSatPP::opt_tare = true; //Experimentally set to true
	MiniSatPP::opt_primes_file = pcsolver->modes().primesfile.c_str();
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

//bool Aggrs::transformOneToOneSetToSignMapping(TypedSet* setone, vps& sets) {
//	vpagg aggs = setone->getAgg();
//
//	vpagg newaggs;
//	newaggs.push_back(aggs[0]);
//	setone->replaceAgg(newaggs);
//
//	TypedSet* settwo = new TypedSet(setone->getSolver(), setone->getSetID());
//	settwo->setWL(setone->getWL());
//
//	for (vpagg::const_iterator i = ++aggs.begin(); i < aggs.end(); i++) {
//		if ((*i)->getSign() == setone->getAgg()[0]->getSign()) {
//			setone->addAgg(*i);
//		} else {
//			settwo->addAgg(*i);
//		}
//	}
//
//	if (settwo->getAgg().size() > 0) {
//		sets.push_back(settwo);
//	} else {
//		delete settwo;
//	}
//	return true;
//}
