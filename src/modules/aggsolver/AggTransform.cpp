/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#include "modules/aggsolver/AggTransform.hpp"

#include <vector>
#include <algorithm>

#include "modules/aggsolver/AggProp.hpp"
#include "modules/aggsolver/AggSet.hpp"
#include "modules/aggsolver/AggPrint.hpp"
#include "modules/aggsolver/AggUtils.hpp"
#include "theorysolvers/PCSolver.hpp"
#include "modules/aggsolver/PartiallyWatched.hpp"

using namespace std;
using namespace MinisatID;

bool compareAggBounds(TempAgg* lhs, TempAgg* rhs) {
	return lhs->getBound() < rhs->getBound();
}

void MinisatID::verifySet(const WLSet& set, AggType type) {
	for (auto i = set.getWL().cbegin(); i < set.getWL().cend(); ++i) {
		if (type == AggType::CARD && (*i).getWeight() != 1) {
			throw idpexception("Cardinality set does not have weights equal to 1.\n");
		}
		if (type == AggType::PROD && (*i).getWeight() < 1) { //Exception if product contains negative/zero weights
			stringstream ss;
			ss << "Error: Set nr. " << set.setID << " contains a 0 (zero) or negative weight " << (*i).getWeight()
					<< ", which cannot occur in a product set.\n";
			throw idpexception(ss.str());
		}
#ifdef NOARBITPREC
		if ((*i).getWeight() == posInfinity() || (*i).getWeight() == negInfinity()) {
			throw idpexception("Weights equal to or larger than the largest integer number "
					"are not allowed in limited precision.\n");
		}
#endif
	}
}

void MinisatID::verifyAggregate(WLSet const * const set, AggType settype, Var head, AggType aggtype) {
	if (settype != aggtype) {
		stringstream ss;
		ss << "Set nr. " << set->setID << " has type " << settype << ", but contains an aggregate over type " << aggtype << ".\n";
		throw idpexception(ss.str());
	}
	for (auto i = set->getWL().cbegin(); i < set->getWL().cend(); ++i) {
		if (var((*i).getLit()) == head) { //Exception if head occurs in set itself
			stringstream ss;
			ss << "Set nr. " << set->setID << " contains a literal of atom " << head << ", the head of an aggregate, which is not allowed.\n";
			throw idpexception(ss.str());
		}
	}
	// TODO remove here if used in propagatorfactory
	verifySet(*set, settype);
}

//@pre: has been split
//@post: set ordered from low to high weights
void MinisatID::setReduce(PCSolver*, WLSet* set, std::vector<TempAgg*>&, const AggProp& type, Weight& knownbound, bool&, bool&) {
	MAssert(set->getWL().size()>0);
	vwl oldset = set->getWL();
	vwl newset;

	knownbound = 0;

	//Sort all wlits according to the integer representation of their literal (to get all literals next to each other)
	std::stable_sort(oldset.begin(), oldset.end(), compareWLByLits<WLtuple>);

	int indexinnew = 0;
	newset.push_back(oldset[indexinnew]);

	bool setisreduced = false;
	for (uint i = 1; i < oldset.size(); ++i) {
		auto oldl = newset[indexinnew];
		auto newl = oldset[i];
		if (var(oldl.getLit()) == var(newl.getLit())) { //same variable
			setisreduced = true;
			if (oldl.getLit() == newl.getLit()) { //same literal, keep combined weight
				auto w = type.getCombinedWeight(newl.getWeight(), oldl.getWeight());
				newset[indexinnew] = WL(oldl.getLit(), w);
			} else { //opposite signs
				newset[indexinnew] = type.handleOccurenceOfBothSigns(oldl, newl, knownbound);
			}
		} else {
			newset.push_back(newl);
			++indexinnew;
		}
	}
	vwl newset2;
	for (vwl::size_type i = 0; i < newset.size(); ++i) {
		if (!type.isNeutralElement(newset[i].getWeight())) {
			newset2.push_back(newset[i]);
		} else {
			setisreduced = true;
		}
	}

	if (setisreduced) {
		set->wl = newset2;
	}
	std::sort(set->wl.begin(), set->wl.end(), compareByWeights<WL>);
}

void MinisatID::addHeadImplications(PCSolver* solver, WLSet*, std::vector<TempAgg*>& aggs, bool&, bool&) {
	if (aggs.size() > 1 && aggs[0]->getSem() != AggSem::IMPLICATION) {
		tempagglist lbaggs, ubaggs;
		for (auto i = aggs.cbegin(); i < aggs.cend(); ++i) {
			if ((*i)->hasLB()) {
				lbaggs.push_back(*i);
			} else {
				ubaggs.push_back(*i);
			}
		}
		if (lbaggs.size() > 1) {
			sort(lbaggs.begin(), lbaggs.end(), compareAggBounds);
			TempAgg* first = *lbaggs.cbegin();
			for (auto i = lbaggs.cbegin() + 1; i < lbaggs.cend(); ++i) {
				TempAgg* second = *i;
				Disjunction disj;
				disj.literals.push_back(first->getHead());
				disj.literals.push_back(not second->getHead());
				solver->add(disj);
				if (first->getBound() == second->getBound()) {
					Disjunction disj2;
					disj2.literals.push_back(not first->getHead());
					disj2.literals.push_back(second->getHead());
					solver->add(disj2);
				}
				first = second;
			}
		}
		if (ubaggs.size() > 1) {
			sort(ubaggs.begin(), ubaggs.end(), compareAggBounds);
			reverse(ubaggs.begin(), ubaggs.end());
			TempAgg* first = *ubaggs.cbegin();
			for (auto i = ubaggs.cbegin() + 1; i < ubaggs.cend(); ++i) {
				TempAgg* second = *i;
				Disjunction disj;
				disj.literals.push_back(first->getHead());
				disj.literals.push_back(not second->getHead());
				solver->add(disj);
				if (first->getBound() == second->getBound()) {
					Disjunction disj2;
					disj2.literals.push_back(not first->getHead());
					disj2.literals.push_back(second->getHead());
					solver->add(disj2);
				}
				first = second;
			}
		}
	}
}

//After type setting and transforming to max
//@ pre: set ordered according to weight!
void MinisatID::max2SAT(PCSolver* solver, WLSet* set, std::vector<TempAgg*>& aggs, bool& unsat, bool& sat) {
	//Simple heuristic to choose for encoding as SAT
	if (aggs.size() != 1 || aggs.front()->getType() != AggType::MAX || aggs[0]->getSem() == AggSem::IMPLICATION) {
		return;
	}

	MAssert(aggs.size()==1);
	/*
	 * For a maximum: if lower,  head <=> conj of negation of all literals with weight higher than bound
	 * 				  if higher, head <=> disj of all literals with weight higher/eq than bound
	 */
	const TempAgg& agg = *aggs[0];
	bool ub = agg.hasUB();
	const Weight& bound = agg.getBound();
	/*	if (agg.isDefined()) { //FIXME add code somewhere else?
	 Rule rule;
	 rule.definitionID = agg.getDefID();
	 rule.head = var(agg.getHead());
	 rule.conjunctive = ub;
	 for (vwl::const_reverse_iterator i = set->getWL().rbegin(); i < set->getWL().rend()	&& (*i).getWeight() >= bound; ++i) {
	 if (ub && (*i).getWeight() == bound) {
	 break;
	 }
	 if (ub) {
	 rule.body.push_back(~(*i).getLit());
	 } else {
	 rule.body.push_back((*i).getLit());
	 }
	 }

	 notunsat = set->getSolver()->getPCSolver().add(rule);
	 } else {*/
	Disjunction clause;
	clause.literals.push_back(ub ? agg.getHead() : not agg.getHead());
	for (auto i = set->getWL().rbegin(); i < set->getWL().rend() && (*i).getWeight() >= bound; ++i) {
		if (ub && (*i).getWeight() == bound) {
			break;
		}
		clause.literals.push_back((*i).getLit());
	}
	solver->add(clause);
	for (vwl::const_reverse_iterator i = set->getWL().rbegin(); i < set->getWL().rend() && (*i).getWeight() >= bound; ++i) {
		if (ub && (*i).getWeight() == bound) {
			break;
		}
		clause.literals.clear();
		clause.literals.push_back(ub ? not agg.getHead() : agg.getHead());
		clause.literals.push_back(not (*i).getLit());
		solver->add(clause);
	}
	//}
	aggs.clear();

	if (solver->satState() == SATVAL::UNSAT) {
		unsat = true;
	} else {
		sat = true; //Encoding succeeded, so aggregate itself can be dropped.
	}
}

/**
 * Rewrites cards as sets of clauses iff:
 * 	bound-esv == 0 && upper => head is always true
 * 	bound-esv == 1 && upper => write out equivalence if not too large
 * 								if large, only write out if head already true
 * 	FUTURE others?
 */
void MinisatID::card2Equiv(PCSolver* solver, WLSet* set, std::vector<TempAgg*>& aggs, const Weight& knownbound, bool& unsat, bool& sat) {
	MAssert(!unsat);
	if (aggs[0]->getType() == AggType::CARD && aggs[0]->getSem() != AggSem::IMPLICATION) {
		tempagglist remaggs;
		for (auto i = aggs.cbegin(); !unsat && i < aggs.cend(); ++i) {
			const TempAgg& agg = *(*i);
			const Weight& bound = agg.getBound() - knownbound;
			if (agg.hasLB() && bound == 0) {
				lbool headvalue = solver->value(agg.getHead());
				if (headvalue != l_False) {
					/*if (agg.getSem() == DEF) {
					 Rule rule;
					 rule.definitionID = agg.getDefID();
					 rule.head = var(agg.getHead());
					 rule.conjunctive = true;
					 unsat = unsat || !set->getSolver()->getPCSolver().add(rule);
					 }else{*/
					if (headvalue == l_Undef) {
						solver->setTrue(agg.getHead(), NULL);
					}
					//}
				}
			} else if (agg.hasLB() && bound == 1) {
				/*if (agg.getSem() == DEF) {
				 Rule rule;
				 rule.definitionID = agg.getDefID();
				 rule.head = var(agg.getHead());
				 rule.conjunctive = false;
				 for (uint j = 0; j < set->getWL().size(); ++j) {
				 rule.body.push_back(set->getWL()[j].getLit());
				 }
				 unsat = !set->getSolver()->getPCSolver().add(rule);
				 } else{*/
				litlist body;
				for (uint j = 0; j < set->getWL().size(); ++j) {
					body.push_back(set->getWL()[j].getLit());
				}
				Implication eq(agg.getHead(), ImplicationType::EQUIVALENT, body, false);
				solver->add(eq);
				//}
			} else {
				remaggs.push_back(*i);
			}
			if (solver->satState() == SATVAL::UNSAT) {
				unsat = true;
			}
		}
		aggs.clear();
		aggs = remaggs;
	}

	if (not unsat && aggs.size() == 0) {
		sat = true;
	}
}

AggProp const * getType(AggType type) {
	switch (type) {
	case AggType::MAX:
		return AggProp::getMax();
		break;
	case AggType::SUM:
		return AggProp::getSum();
		break;
	case AggType::CARD:
		return AggProp::getCard();
		break;
	case AggType::PROD:
		return AggProp::getProd();
		break;
	default:
		throw idpexception("Encountered a bug in the code which transforms aggregates.\n");
	}
}

TypedSet* createPropagator(PCSolver* solver, WLSet* set, const std::vector<TempAgg*>& aggs, const Weight& knownbound, bool usewatches,
		bool optim) {
	return new TypedSet(solver, set->setID, knownbound, getType(aggs.front()->getType()), set->getWL(), usewatches, aggs, optim);
}

void MinisatID::decideUsingWatchesAndCreateOptimPropagator(PCSolver* solver, WLSet* set, TempAgg* agg, const Weight& knownbound) {
	// Set correct upper bound:
	agg->setBound(AggBound(AggSign::UB, getType(agg->getType())->getMaxPossible(set->getWL())));

	double ratio = testGenWatchCount(*solver, *set, *getType(agg->getType()), tempagglist { agg }, knownbound);
	// FIXME for watched datastructs, the (re)initialize is not correct
	auto typedset = createPropagator(solver, set, tempagglist { agg }, knownbound, ratio < solver->modes().watchesratio, true);

	solver->addAggOptimization(typedset->getAgg().front());
}

void MinisatID::decideUsingWatchesAndCreatePropagators(PCSolver* solver, WLSet* set, const std::vector<TempAgg*>& aggs,
		const Weight& knownbound) {
	bool watchable = true;
	MAssert(aggs.size()>0);
	auto type = aggs.front()->getType();
	for (auto i = aggs.cbegin(); i < aggs.cend(); ++i) {
		if ((*i)->getType() == AggType::MAX) {
			watchable = false;
		}
	}
	if (not watchable) {
		createPropagator(solver, set, aggs, knownbound, false, false);
		return;
	}

	MAssert(aggs[0]->getSem()!=AggSem::IMPLICATION);
	// TODO add to other transformations!

	//create implication aggs
	tempagglist implaggs, del;
	for (auto i = aggs.cbegin(); i < aggs.cend(); ++i) {
		const TempAgg& agg = *(*i);

		TempAgg *one, *two;
		Weight weighttwo = agg.getSign() == AggSign::LB ? agg.getBound() - 1 : agg.getBound() + 1;
		AggSign signtwo = agg.getSign() == AggSign::LB ? AggSign::UB : AggSign::LB;
		one = new TempAgg(~agg.getHead(), AggBound(agg.getSign(), agg.getBound()), AggSem::IMPLICATION, agg.getType());
		two = new TempAgg(agg.getHead(), AggBound(signtwo, weighttwo), AggSem::IMPLICATION, agg.getType());

		implaggs.push_back(one);
		implaggs.push_back(two);
		del.push_back(*i);
	}

	//separate in both signs
	tempagglist signoneaggs, signtwoaggs;
	signoneaggs.push_back(implaggs[0]);
	for (auto i = ++implaggs.cbegin(); i < implaggs.cend(); ++i) {
		if ((*i)->getSign() == implaggs[0]->getSign()) {
			signoneaggs.push_back(*i);
		} else {
			signtwoaggs.push_back(*i);
		}
	}

	//for each, generate watches and count ratio
	//		partially watched and add sets in new format!
	MAssert(signoneaggs.size()>0);
	double ratioone = testGenWatchCount(*solver, *set, *getType(type), signoneaggs, knownbound);
	double ratiotwo = 0;
	if (signtwoaggs.size() > 0) {
		ratiotwo = testGenWatchCount(*solver, *set, *getType(type), signtwoaggs, knownbound);
	}

	// Create propagators
	double ratio = ratioone * 0.5 + ratiotwo * 0.5;
	if (ratio < solver->modes().watchesratio) { // FIXME NOTE it has to be disequality, because there are some cases in which ratio can be 0
		createPropagator(solver, set, signoneaggs, knownbound, true, false);
		if (signtwoaggs.size() > 0) {
			createPropagator(solver, set, signtwoaggs, knownbound, true, false);
		}
	} else {
		createPropagator(solver, set, aggs, knownbound, false, false);
	}
}
