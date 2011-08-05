/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#include "AggTransform.hpp"

#include <vector>
#include <algorithm>

#include "modules/aggsolver/AggProp.hpp"
#include "modules/aggsolver/AggSet.hpp"
#include "modules/aggsolver/AggPrint.hpp"
#include "modules/aggsolver/AggUtils.hpp"
#include "theorysolvers/PCSolver.hpp"
#include "modules/aggsolver/PartiallyWatched.hpp"

#include "PbSolver.h"

using namespace std;
using namespace MinisatID;

class OrderedAggTransformations{
public:
	std::vector<AggTransformation*> t;

	OrderedAggTransformations(){
		t.push_back(new PartitionIntoTypes());
		t.push_back(new MinToMax());
		t.push_back(new AddTypes());
		t.push_back(new VerifyWeights());
		t.push_back(new MaxToSAT());
		t.push_back(new SetReduce());
		t.push_back(new CardToEquiv());
		t.push_back(new AddHeadImplications());
		//t.push_back(new MapToSetOneToOneWithAgg());
		t.push_back(new MapToSetWithSameAggSign());
	}
	~OrderedAggTransformations(){
		deleteList<AggTransformation>(t);
	}
};

OrderedAggTransformations transfo;

const vector<AggTransformation*>& MinisatID::getTransformations(){
	return transfo.t;
}

//@pre: has been split
void SetReduce::transform(PCSolver* solver, TypedSet* set, bool& unsat, bool& sat) const {
	vwl oldset = set->getWL();
	vwl newset;

	//Sort all wlits according to the integer representation of their literal (to get all literals next to each other)
	std::stable_sort(oldset.begin(), oldset.end(), compareWLByLits);

	int indexinnew = 0;
	newset.push_back(oldset[indexinnew]);

	bool setisreduced = false;
	for (vsize i = 1; i < oldset.size(); ++i) {
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
			++indexinnew;
		}
	}

	vwl newset2;
	bool canbecard = true;
	for (vwl::size_type i = 0; i < newset.size(); ++i) {
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
			for (agglist::const_iterator i = set->getAgg().begin(); i < set->getAgg().end(); ++i) {
				if ((*i)->getType() == SUM) {
					(*i)->setType(CARD);
				}
			}
		}
	} else {
		if(set->getType().getType()==CARD){
			set->setType(AggProp::getSum());
			for (agglist::const_iterator i = set->getAgg().begin(); i < set->getAgg().end(); ++i) {
				if ((*i)->getType() == CARD) {
					(*i)->setType(SUM);
				}
			}
		}
	}
}

void MapToSetOneToOneWithAgg::transform(PCSolver* solver, TypedSet* set, bool& unsat, bool& sat) const {
	if(!set->isUsingWatches() || set->getAgg().size()==1){
		return;
	}

	agglist aggs = set->getAgg();
	assert(aggs.size()>0);

	agglist newaggs;
	newaggs.push_back(aggs[0]);
	set->replaceAgg(newaggs);

	for (agglist::const_iterator i = ++aggs.begin(); i < aggs.end(); ++i) {
		// FIXME
		/*TypedSet* newset = new TypedSet(*set);
		newset->addAgg(*i);
		assert(newset->getAgg().size()==1);
		sets.push_back(newset);*/
	}
	assert(set->getAgg().size()==1);
}

void MapToSetWithSameAggSign::transform(PCSolver* solver, TypedSet* set, bool& unsat, bool& sat) const {
	bool watchable = true;
	for(vector<Agg*>::const_iterator i=set->getAgg().begin(); i<set->getAgg().end(); ++i){
		if((*i)->getType()==MAX){
			watchable = false;
		}
	}
	if(!watchable){
		set->setUsingWatches(false);
	}
	if(!set->isUsingWatches()){
		return;
	}

	assert(set->getAgg()[0]->getSem()!=IMPLICATION); //FIXME add to other transformations!

	//create implication aggs
	agglist implaggs, del;
	for(agglist::const_iterator i=set->getAgg().begin(); i<set->getAgg().end(); ++i){
		const Agg& agg = *(*i);

		Agg *one, *two;
		Weight weighttwo = agg.getSign()==AGGSIGN_LB?agg.getBound()-1:agg.getBound()+1;
		AggSign signtwo = agg.getSign()==AGGSIGN_LB?AGGSIGN_UB:AGGSIGN_LB;
		one = new Agg(~agg.getHead(), AggBound(agg.getSign(), agg.getBound()), IMPLICATION, agg.getType());
		two = new Agg(agg.getHead(), AggBound(signtwo, weighttwo), IMPLICATION, agg.getType());

		implaggs.push_back(one);
		implaggs.push_back(two);
		del.push_back(*i);
	}

	//separate in both signs
	agglist signoneaggs, signtwoaggs;
	signoneaggs.push_back(implaggs[0]);
	for (agglist::const_iterator i = ++implaggs.begin(); i < implaggs.end(); ++i) {
		if ((*i)->getSign() == implaggs[0]->getSign()) {
			signoneaggs.push_back(*i);
		} else {
			signtwoaggs.push_back(*i);
		}
	}

	//for each, generate watches and count ratio
	// FIXME add sets in new format!
/*	TypedSet* signoneset = new TypedSet(*set);
	signoneset->replaceAgg(signoneaggs);
	GenPWAgg* propone = new GenPWAgg(signoneset);
	signoneset->setProp(propone);
	double ratioone = propone->testGenWatchCount();

	double ratiotwo = 0;
	TypedSet* signtwoset = NULL;
	if(signtwoaggs.size()>0){
		signtwoset = new TypedSet(*set);
		signtwoset->replaceAgg(signtwoaggs);
		GenPWAgg* proptwo = new GenPWAgg(signtwoset);
		signtwoset->setProp(proptwo);
		ratiotwo = proptwo->testGenWatchCount();
	}

	double ratio = ratioone*0.5+ratiotwo*0.5;
	if(ratio<=solver->modes().watchesratio){
		if(signtwoset!=NULL){
			agglist empty;
			signtwoset->replaceAgg(empty);
			set->replaceAgg(signtwoaggs, del);
			delete propone;
			signoneset->setProp(NULL);
			sets.push_back(signoneset);
		}else{
			agglist empty;
			signoneset->replaceAgg(empty);
			set->replaceAgg(signoneaggs, del);
			delete signoneset;
		}
	}else{
		set->setUsingWatches(false);
		delete signoneset;
	}
	if(signtwoset!=NULL){
		delete signtwoset;
	}*/
}

void PartitionIntoTypes::transform(PCSolver* solver, TypedSet* set, bool& unsat, bool& sat) const {
	if(set->getAgg().size()==0){
		sat = true;
		return;
	}
	//Partition the aggregates according to their type
	map<AggType, agglist> partaggs;
	for (agglist::const_iterator i = set->getAgg().begin(); i < set->getAgg().end(); ++i) {
		partaggs[(*i)->getType()].push_back(*i);
	}

	map<AggType, agglist>::const_iterator i = partaggs.begin();
	set->replaceAgg((*i).second);
	++i;
	for (; i != partaggs.end(); ++i) {
		// FIXME
		/*TypedSet* newset = new TypedSet(*set);
		assert((*i).second.size()>0);
		newset->replaceAgg((*i).second);
		newset->setWL(set->getWL());
		sets.push_back(newset);*/
	}
}

bool compareAggBounds(Agg* lhs, Agg* rhs){
	return lhs->getCertainBound() < rhs->getCertainBound();
}

void AddHeadImplications::transform(PCSolver* solver, TypedSet* set, bool& unsat, bool& sat) const {
	if(set->getAgg().size()>1 && set->getAgg()[0]->getSem()!=IMPLICATION){
		agglist lbaggs, ubaggs;
		for(agglist::const_iterator i=set->getAgg().begin(); i<set->getAgg().end(); ++i){
			if((*i)->hasLB()){
				lbaggs.push_back(*i);
			}else{
				ubaggs.push_back(*i);
			}
		}
		if(lbaggs.size()>1){
			sort(lbaggs.begin(),lbaggs.end(), compareAggBounds);
			Agg* first = *lbaggs.begin();
			for(agglist::const_iterator i=lbaggs.begin()+1; i<lbaggs.end(); ++i){
				Agg* second = *i;
				InnerDisjunction disj;
				disj.literals.push(first->getHead());
				disj.literals.push(~second->getHead());
				solver->add(disj);
				if(first->getCertainBound()==second->getCertainBound()){
					InnerDisjunction disj2;
					disj2.literals.push(~first->getHead());
					disj2.literals.push(second->getHead());
					solver->add(disj2);
				}
				first = second;
			}
		}
		if(ubaggs.size()>1){
			sort(ubaggs.begin(),ubaggs.end(), compareAggBounds);
			reverse(ubaggs.begin(), ubaggs.end());
			Agg* first = *ubaggs.begin();
			for(agglist::const_iterator i=ubaggs.begin()+1; i<ubaggs.end(); ++i){
				Agg* second = *i;
				InnerDisjunction disj;
				disj.literals.push(first->getHead());
				disj.literals.push(~second->getHead());
				solver->add(disj);
				if(first->getCertainBound()==second->getCertainBound()){
					InnerDisjunction disj2;
					disj2.literals.push(~first->getHead());
					disj2.literals.push(second->getHead());
					solver->add(disj2);
				}
				first = second;
			}
		}
	}
}

//@pre Has to be split
void VerifyWeights::transform(PCSolver* solver, TypedSet* set, bool& unsat, bool& sat) const {
	if (set->getAgg()[0]->getType() == PROD) {
		for (vsize i = 0; i < set->getWL().size(); ++i) {
			if (set->getWL()[i] < 1) { //Exception if product contains negative/zero weights
				char s[200];
				sprintf(s, "Error: Set nr. %d contains a 0 (zero) or negative weight %s, which cannot "
					"be used in combination with a product aggregate\n", set->getSetID(), toString(
						set->getWL()[i].getWeight()).c_str());
				throw idpexception(s);
			}
		}
	}
}

//@pre Has to be split
//Adds the type objects and correct esv to the sets
void AddTypes::transform(PCSolver* solver, TypedSet* set, bool& unsat, bool& sat) const {
	switch (set->getAgg()[0]->getType()) {
		case MAX:
			set->setType(AggProp::getMax());
			break;
		case SUM:
			set->setType(AggProp::getSum());
			break;
		case CARD:
			set->setType(AggProp::getCard());
			break;
		case PROD:
			set->setType(AggProp::getProd());
			break;
		default:
			assert(false);
	}
}

void MinToMax::transform(PCSolver* solver, TypedSet* set, bool& unsat, bool& sat) const {
	if (set->getAgg()[0]->getType() == MIN) {
		//Transform Min into Max set: invert all weights
		vwl wl;
		for (vsize i = 0; i < set->getWL().size(); ++i) {
			wl.push_back(WL(set->getWL()[i].getLit(), -set->getWL()[i].getWeight()));
		}
		set->setWL(wl);

		//Invert the bound of all the aggregates involved
		for (agglist::const_iterator i = set->getAgg().begin(); i < set->getAgg().end(); ++i) {
			Weight bound = -(*i)->getBound();
			AggSign sign = (*i)->getSign()==AGGSIGN_LB?AGGSIGN_UB:AGGSIGN_LB;
			(*i)->setBound(AggBound(sign, bound));
			assert((*i)->getType()==MIN);
			(*i)->setType(MAX);
		}
	}
}

//After type setting and transforming to max
void MaxToSAT::transform(PCSolver* solver, TypedSet* set, bool& unsat, bool& sat) const {
	//Simple heuristic to choose for encoding as SAT
	if (set->getType().getType()!=MAX || set->getAgg().size() != 1 || set->getAgg()[0]->getSem()==IMPLICATION) {
		return;
	}

	bool notunsat = true;
	assert( set->getAgg().size()==1);
	/*
	 * For a maximum: if lower,  head <=> conj of negation of all literals with weight higher than bound
	 * 				  if higher, head <=> disj of all literals with weight higher/eq than bound
	 */
	const Agg& agg = *set->getAgg()[0];
	bool ub = agg.hasUB();
	const Weight& bound = agg.getBound();
/*	if (agg.isDefined()) { //FIXME add code somewhere else?
		InnerRule rule;
		rule.definitionID = agg.getDefID();
		rule.head = var(agg.getHead());
		rule.conjunctive = ub;
		for (vwl::const_reverse_iterator i = set->getWL().rbegin(); i < set->getWL().rend()	&& (*i).getWeight() >= bound; ++i) {
			if (ub && (*i).getWeight() == bound) {
				break;
			}
			if (ub) {
				rule.body.push(~(*i).getLit());
			} else {
				rule.body.push((*i).getLit());
			}
		}

		notunsat = set->getSolver()->getPCSolver().add(rule);
	} else {*/
		InnerDisjunction clause;
		clause.literals.push(ub? agg.getHead():~agg.getHead());
		for (vwl::const_reverse_iterator i = set->getWL().rbegin(); i < set->getWL().rend()	&& (*i).getWeight() >= bound; ++i) {
			if (ub && (*i).getWeight() == bound) {
				break;
			}
			clause.literals.push((*i).getLit());
		}
		notunsat = solver->add(clause);
		for (vwl::const_reverse_iterator i = set->getWL().rbegin(); notunsat && i < set->getWL().rend()
					&& (*i).getWeight() >= bound; ++i) {
			if (ub && (*i).getWeight() == bound) {
				break;
			}
			clause.literals.clear();
			clause.literals.push(ub?~agg.getHead():agg.getHead());
			clause.literals.push(~(*i).getLit());
			notunsat = solver->add(clause);
		}
	//}
	set->replaceAgg(vector<Agg*>());

	if(notunsat){
		sat = true; //Encoding succeeded, so aggregate itself can be dropped.
	}else{
		unsat = true;
	}
}

/**
 * Rewrites cards as sets of clauses iff:
 * 	bound-esv == 0 && upper => head is always true
 * 	bound-esv == 1 && upper => write out equivalence if not too large
 * 								if large, only write out if head already true
 * 	FUTURE others?
 */
void CardToEquiv::transform(PCSolver* solver, TypedSet* set, bool& unsat, bool& sat) const {
	assert(!unsat);
	if (set->getAgg()[0]->getType() == CARD && set->getAgg()[0]->getSem()!=IMPLICATION) {
		agglist remaggs;
		for (agglist::const_iterator i = set->getAgg().begin(); !unsat && i < set->getAgg().end(); ++i) {
			const Agg& agg = *(*i);
			const Weight& bound = agg.getCertainBound();
			if(agg.hasLB() && bound==0){
				lbool headvalue = solver->value(agg.getHead());
				if(headvalue==l_False){
					unsat = true;
				}else{
					/*if (agg.getSem() == DEF) {
						InnerRule rule;
						rule.definitionID = agg.getDefID();
						rule.head = var(agg.getHead());
						rule.conjunctive = true;
						unsat = unsat || !set->getSolver()->getPCSolver().add(rule);
					}else{*/
						if(headvalue==l_Undef){
							solver->setTrue(agg.getHead(), set);
						}
					//}
				}
			}else if(agg.hasLB() && bound==1){
				/*if (agg.getSem() == DEF) {
					InnerRule rule;
					rule.definitionID = agg.getDefID();
					rule.head = var(agg.getHead());
					rule.conjunctive = false;
					for (vsize j = 0; j < set->getWL().size(); ++j) {
						rule.body.push(set->getWL()[j].getLit());
					}
					unsat = !set->getSolver()->getPCSolver().add(rule);
				} else{*/
					InnerEquivalence eq;
					eq.head = agg.getHead();
					eq.conjunctive = false;
					for (vsize j = 0; j < set->getWL().size(); ++j) {
						eq.literals.push(set->getWL()[j].getLit());
					}
					unsat = !solver->add(eq);
				//}
			}else{
				remaggs.push_back(*i);
			}
		}
		set->replaceAgg(remaggs);
	}

	if(!unsat && set->getAgg().size()==0){
		sat = true;
	}
}
