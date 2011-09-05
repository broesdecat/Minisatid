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

#include "PbSolver.h"

using namespace std;
using namespace MinisatID;

bool compareAggBounds(TempAgg* lhs, TempAgg* rhs){
	return lhs->getBound() < rhs->getBound();
}

void MinisatID::verifySet(const InnerWLSet& set){
	for(auto i=set.wls.begin(); i<set.wls.end(); ++i) {
		if(set.type == CARD && (*i).getWeight()!=1) {
			throw idpexception("Cardinality set does not have weights equal to 1.\n");
		}
		if(set.type == PROD && (*i).getWeight() < 1) { //Exception if product contains negative/zero weights
			stringstream ss;
			ss <<"Error: Set nr. " <<set.setID  <<" contains a 0 (zero) or negative weight " <<(*i).getWeight()
					<< ", which cannot occur in a product set.\n";
			throw idpexception(ss.str());
		}
#ifdef NOARBITPREC
		if((*i).getWeight() == posInfinity() || (*i).getWeight() == negInfinity()){
			throw idpexception(
				"Weights equal to or larger than the largest integer number "
				"are not allowed in limited precision.\n");
		}
#endif
	}
}

void MinisatID::verifyAggregate(InnerWLSet const * const set, Var head, AggType aggtype){
	if(set->type!=aggtype){
		stringstream ss;
		ss <<"Set nr. " <<set->setID <<" has type " <<set->type <<", but contains an aggregate over type " <<aggtype <<".\n";
		throw idpexception(ss.str());
	}
	for(auto i=set->wls.begin(); i<set->wls.end(); ++i) {
		if (var((*i).getLit()) == head) { //Exception if head occurs in set itself
			stringstream ss;
			ss <<"Set nr. " <<set->setID <<" contains a literal of atom " <<head <<", the head of an aggregate, which is not allowed.\n";
			throw idpexception(ss.str());
		}
	}
	// TODO remove here if used in propagatorfactory
	verifySet(*set);
}

//@pre: has been split
//@post: set ordered from low to high weights
void MinisatID::setReduce(PCSolver* solver, InnerWLSet* set, std::vector<TempAgg*>& aggs, const AggProp& type, Weight& knownbound, bool& unsat, bool& sat){
	assert(!unsat && !sat && aggs.size()>0);
	vwl oldset = set->wls;
	vwl newset;

	knownbound = 0;

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
				Weight w = type.getCombinedWeight(newl.getWeight(), oldl.getWeight());
				newset[indexinnew] = WL(oldl.getLit(), w);
			} else { //opposite signs
				WL wl = type.handleOccurenceOfBothSigns(oldl, newl, knownbound);
				newset[indexinnew] = WL(wl.getLit(), wl.getWeight());
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
		set->wls = newset2;
	}

	std::sort(set->wls.begin(), set->wls.end(), compareByWeights<WL>);
}

void MinisatID::addHeadImplications(PCSolver* solver, InnerWLSet* set, std::vector<TempAgg*>& aggs, bool& unsat, bool& sat) {
	assert(!unsat && !sat && aggs.size()>0);
	if(aggs.size()>1 && aggs[0]->getSem()!=IMPLICATION){
		tempagglist lbaggs, ubaggs;
		for(auto i=aggs.begin(); i<aggs.end(); ++i){
			if((*i)->hasLB()){
				lbaggs.push_back(*i);
			}else{
				ubaggs.push_back(*i);
			}
		}
		if(lbaggs.size()>1){
			sort(lbaggs.begin(),lbaggs.end(), compareAggBounds);
			TempAgg* first = *lbaggs.begin();
			for(auto i=lbaggs.begin()+1; i<lbaggs.end(); ++i){
				TempAgg* second = *i;
				InnerDisjunction disj;
				disj.literals.push_back(first->getHead());
				disj.literals.push_back(not second->getHead());
				solver->add(disj);
				if(first->getBound()==second->getBound()){
					InnerDisjunction disj2;
					disj2.literals.push_back(not first->getHead());
					disj2.literals.push_back(second->getHead());
					solver->add(disj2);
				}
				first = second;
			}
		}
		if(ubaggs.size()>1){
			sort(ubaggs.begin(),ubaggs.end(), compareAggBounds);
			reverse(ubaggs.begin(), ubaggs.end());
			TempAgg* first = *ubaggs.begin();
			for(auto i=ubaggs.begin()+1; i<ubaggs.end(); ++i){
				TempAgg* second = *i;
				InnerDisjunction disj;
				disj.literals.push_back(first->getHead());
				disj.literals.push_back(not second->getHead());
				solver->add(disj);
				if(first->getBound()==second->getBound()){
					InnerDisjunction disj2;
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
void MinisatID::max2SAT(PCSolver* solver, InnerWLSet* set, std::vector<TempAgg*>& aggs, bool& unsat, bool& sat) {
	//Simple heuristic to choose for encoding as SAT
	if (set->type!=MAX || aggs.size() != 1 || aggs[0]->getSem()==IMPLICATION) {
		return;
	}

	assert(aggs.size()==1);
	/*
	 * For a maximum: if lower,  head <=> conj of negation of all literals with weight higher than bound
	 * 				  if higher, head <=> disj of all literals with weight higher/eq than bound
	 */
	const TempAgg& agg = *aggs[0];
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
				rule.body.push_back(~(*i).getLit());
			} else {
				rule.body.push_back((*i).getLit());
			}
		}

		notunsat = set->getSolver()->getPCSolver().add(rule);
	} else {*/
		InnerDisjunction clause;
		clause.literals.push_back(ub? agg.getHead():not agg.getHead());
		for (vwl::const_reverse_iterator i = set->wls.rbegin(); i < set->wls.rend()	&& (*i).getWeight() >= bound; ++i) {
			if (ub && (*i).getWeight() == bound) {
				break;
			}
			clause.literals.push_back((*i).getLit());
		}
		solver->add(clause);
		for (vwl::const_reverse_iterator i = set->wls.rbegin(); i < set->wls.rend()
					&& (*i).getWeight() >= bound; ++i) {
			if (ub && (*i).getWeight() == bound) {
				break;
			}
			clause.literals.clear();
			clause.literals.push_back(ub?not agg.getHead():agg.getHead());
			clause.literals.push_back(not (*i).getLit());
			solver->add(clause);
		}
	//}
	aggs.clear();

	if(solver->isUnsat()){
		unsat = true;
	}else{
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
void MinisatID::card2Equiv(PCSolver* solver, InnerWLSet* set, std::vector<TempAgg*>& aggs, const Weight& knownbound, bool& unsat, bool& sat) {
	assert(!unsat);
	if (aggs[0]->getType() == CARD && aggs[0]->getSem()!=IMPLICATION) {
		tempagglist remaggs;
		for (auto i = aggs.begin(); !unsat && i < aggs.end(); ++i) {
			const TempAgg& agg = *(*i);
			const Weight& bound = agg.getBound()-knownbound;
			if(agg.hasLB() && bound==0){
				lbool headvalue = solver->value(agg.getHead());
				if(headvalue!=l_False){
					/*if (agg.getSem() == DEF) {
						InnerRule rule;
						rule.definitionID = agg.getDefID();
						rule.head = var(agg.getHead());
						rule.conjunctive = true;
						unsat = unsat || !set->getSolver()->getPCSolver().add(rule);
					}else{*/
						if(headvalue==l_Undef){
							solver->setTrue(agg.getHead(), NULL);
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
						rule.body.push_back(set->getWL()[j].getLit());
					}
					unsat = !set->getSolver()->getPCSolver().add(rule);
				} else{*/
					InnerEquivalence eq;
					eq.head = agg.getHead();
					eq.conjunctive = false;
					for (vsize j = 0; j < set->wls.size(); ++j) {
						eq.literals.push_back(set->wls[j].getLit());
					}
					solver->add(eq);
				//}
			}else{
				remaggs.push_back(*i);
			}
			if(solver->isUnsat()){
				unsat = true;
			}
		}
		aggs.clear();
		aggs = remaggs;
	}

	if(not unsat && aggs.size()==0){
		sat = true;
	}
}

AggProp const * getType(AggType type){
	switch (type) {
		case MAX:
			return AggProp::getMax(); break;
		case SUM:
			return AggProp::getSum(); break;
		case CARD:
			return AggProp::getCard(); break;
		case PROD:
			return AggProp::getProd(); break;
		default:
			throw idpexception("Encountered a bug in the code which transforms aggregates.\n");
	}
}

void createPropagator(PCSolver* solver, InnerWLSet* set, const std::vector<TempAgg*>& aggs, const Weight& knownbound, bool usewatches){
	TypedSet* propagator = new TypedSet(solver, set->setID, knownbound);
	propagator->setUsingWatches(usewatches);
	propagator->setWL(set->wls);
	propagator->setType(getType(set->type));
	for(auto agg=aggs.begin(); agg!=aggs.end(); ++agg){
		propagator->addAgg(**agg);
	}
}

void MinisatID::decideUsingWatchesAndCreatePropagators(PCSolver* solver, InnerWLSet* set, const std::vector<TempAgg*>& aggs, const Weight& knownbound){
	bool watchable = true;
	assert(aggs.size()>0);
	for(auto i=aggs.begin(); i<aggs.end(); ++i){
		if((*i)->getType()==MAX){
			watchable = false;
		}
	}
	if(!watchable){
		return;
	}

	assert(aggs[0]->getSem()!=IMPLICATION); // TODO add to other transformations!

	//create implication aggs
	tempagglist implaggs, del;
	for(auto i=aggs.begin(); i<aggs.end(); ++i){
		const TempAgg& agg = *(*i);

		TempAgg *one, *two;
		Weight weighttwo = agg.getSign()==AGGSIGN_LB?agg.getBound()-1:agg.getBound()+1;
		AggSign signtwo = agg.getSign()==AGGSIGN_LB?AGGSIGN_UB:AGGSIGN_LB;
		one = new TempAgg(~agg.getHead(), AggBound(agg.getSign(), agg.getBound()), IMPLICATION, agg.getType());
		two = new TempAgg(agg.getHead(), AggBound(signtwo, weighttwo), IMPLICATION, agg.getType());

		implaggs.push_back(one);
		implaggs.push_back(two);
		del.push_back(*i);
	}

	//separate in both signs
	tempagglist signoneaggs, signtwoaggs;
	signoneaggs.push_back(implaggs[0]);
	for (auto i = ++implaggs.begin(); i < implaggs.end(); ++i) {
		if ((*i)->getSign() == implaggs[0]->getSign()) {
			signoneaggs.push_back(*i);
		} else {
			signtwoaggs.push_back(*i);
		}
	}

	//for each, generate watches and count ratio
	//		partially watched and add sets in new format!
	assert(signoneaggs.size()>0);
	double ratioone = testGenWatchCount(*solver, *set, *getType(set->type), signoneaggs, knownbound);
	double ratiotwo = 0;
	if(signtwoaggs.size()>0){
		ratiotwo = testGenWatchCount(*solver, *set, *getType(set->type), signtwoaggs, knownbound);
	}

	// Create propagators
	double ratio = ratioone*0.5+ratiotwo*0.5;
	if(ratio<=solver->modes().watchesratio){
		createPropagator(solver, set, signoneaggs, knownbound, true);
		if(signtwoaggs.size()>0){
			createPropagator(solver, set, signtwoaggs, knownbound, true);
		}
	}else{
		createPropagator(solver, set, aggs, knownbound, false);
	}
}

//
//class OrderedAggTransformations{
//public:
//	std::vector<AggTransformation*> t;
//
//	OrderedAggTransformations(){
//		t.push_back(new PartitionIntoTypes()); // add as inputformat invariant? => set has type!
//		t.push_back(new MinToMax()); // can be in init
//		t.push_back(new AddTypes()); // part of the invariant then => set has type
//		t.push_back(new VerifyWeights()); // can be in init
//		t.push_back(new MaxToSAT()); // can be on a per-aggregate basis (so also in init)
//		t.push_back(new SetReduce()); // does not create extra sets
//		t.push_back(new CardToEquiv()); // can be on a per-aggregate basis
//		t.push_back(new AddHeadImplications()); // do not change set
//		//t.push_back(new MapToSetOneToOneWithAgg());
//		t.push_back(new MapToSetWithSameAggSign()); // => creates 1 extra set
//	}
//	~OrderedAggTransformations(){
//		deleteList<AggTransformation>(t);
//	}
//};
//
//OrderedAggTransformations transfo;
//
//const vector<AggTransformation*>& MinisatID::getTransformations(){
//	return transfo.t;
//}
//
//
//
//void MapToSetOneToOneWithAgg::transform(PCSolver* solver, TypedSet* set, bool& unsat, bool& sat) const {
//	assert(!unsat && !sat && set->getAgg().size()>0);
//	if(!set->isUsingWatches() || set->getAgg().size()==1){
//		return;
//	}
//
//	agglist aggs = set->getAgg();
//	assert(aggs.size()>0);
//
//	agglist newaggs;
//	newaggs.push_back(aggs[0]);
//	set->replaceAgg(newaggs);
//
//	for (agglist::const_iterator i = ++aggs.begin(); i < aggs.end(); ++i) {
//		TypedSet* newset = new TypedSet(*set);
//		newset->addAgg(*i);
//		assert(newset->getAgg().size()==1);
//		// insert again sets.push_back(newset);
//	}
//	assert(set->getAgg().size()==1);
//}
//
//void MapToSetWithSameAggSign::transform(PCSolver* solver, TypedSet* set, bool& unsat, bool& sat) const {
//	bool watchable = true;
//	assert(!unsat && !sat && set->getAgg().size()>0);
//	for(vector<TempAgg*>::const_iterator i=set->getAgg().begin(); i<set->getAgg().end(); ++i){
//		if((*i)->getType()==MAX){
//			watchable = false;
//		}
//	}
//	if(!watchable){
//		set->setUsingWatches(false);
//	}
//	if(!set->isUsingWatches()){
//		return;
//	}
//
//	assert(set->getAgg()[0]->getSem()!=IMPLICATION); //add to other transformations!
//
//	//create implication aggs
//	agglist implaggs, del;
//	for(agglist::const_iterator i=set->getAgg().begin(); i<set->getAgg().end(); ++i){
//		const Agg& agg = *(*i);
//
//		Agg *one, *two;
//		Weight weighttwo = agg.getSign()==AGGSIGN_LB?agg.getBound()-1:agg.getBound()+1;
//		AggSign signtwo = agg.getSign()==AGGSIGN_LB?AGGSIGN_UB:AGGSIGN_LB;
//		one = new Agg(~agg.getHead(), AggBound(agg.getSign(), agg.getBound()), IMPLICATION, agg.getType());
//		two = new Agg(agg.getHead(), AggBound(signtwo, weighttwo), IMPLICATION, agg.getType());
//
//		implaggs.push_back(one);
//		implaggs.push_back(two);
//		del.push_back(*i);
//	}
//
//	//separate in both signs
//	agglist signoneaggs, signtwoaggs;
//	signoneaggs.push_back(implaggs[0]);
//	for (agglist::const_iterator i = ++implaggs.begin(); i < implaggs.end(); ++i) {
//		if ((*i)->getSign() == implaggs[0]->getSign()) {
//			signoneaggs.push_back(*i);
//		} else {
//			signtwoaggs.push_back(*i);
//		}
//	}
//
//	//for each, generate watches and count ratio
//	//		partially watched and add sets in new format!
///*	TypedSet* signoneset = new TypedSet(*set);
//	signoneset->replaceAgg(signoneaggs);
//	GenPWAgg* propone = new GenPWAgg(signoneset);
//	signoneset->setProp(propone);
//	double ratioone = propone->testGenWatchCount();
//
//	double ratiotwo = 0;
//	TypedSet* signtwoset = NULL;
//	if(signtwoaggs.size()>0){
//		signtwoset = new TypedSet(*set);
//		signtwoset->replaceAgg(signtwoaggs);
//		GenPWAgg* proptwo = new GenPWAgg(signtwoset);
//		signtwoset->setProp(proptwo);
//		ratiotwo = proptwo->testGenWatchCount();
//	}
//
//	double ratio = ratioone*0.5+ratiotwo*0.5;
//	if(ratio<=solver->modes().watchesratio){
//		if(signtwoset!=NULL){
//			agglist empty;
//			signtwoset->replaceAgg(empty);
//			set->replaceAgg(signtwoaggs, del);
//			delete propone;
//			signoneset->setProp(NULL);
//			sets.push_back(signoneset);
//		}else{
//			agglist empty;
//			signoneset->replaceAgg(empty);
//			set->replaceAgg(signoneaggs, del);
//			delete signoneset;
//		}
//	}else{*/
//		set->setUsingWatches(false);
//	/*	delete signoneset;
//	}
//	if(signtwoset!=NULL){
//		delete signtwoset;
//	}*/
//}
//
//void PartitionIntoTypes::transform(PCSolver* solver, TypedSet* set, bool& unsat, bool& sat) const {
//	if(set->getAgg().size()==0){
//		sat = true;
//		return;
//	}
//	//Partition the aggregates according to their type
//	map<AggType, agglist> partaggs;
//	for (agglist::const_iterator i = set->getAgg().begin(); i < set->getAgg().end(); ++i) {
//		partaggs[(*i)->getType()].push_back(*i);
//	}
//
//	map<AggType, agglist>::const_iterator i = partaggs.begin();
//	set->replaceAgg((*i).second);
//	++i;
//	for (; i != partaggs.end(); ++i) {
//		TypedSet* newset = new TypedSet(*set);
//		assert((*i).second.size()>0);
//		newset->replaceAgg((*i).second);
//		newset->setWL(set->getWL());
//		// insert again sets.push_back(newset);
//	}
//}
//
//
////@pre Has to be split
//
//
////@pre Has to be split
////Adds the type objects and correct esv to the sets
//void AddTypes::transform(PCSolver* solver, TypedSet* set, bool& unsat, bool& sat) const {
//	switch (set->getAgg()[0]->getType()) {
//		case MAX:
//			set->setType(AggProp::getMax());
//			break;
//		case SUM:
//			set->setType(AggProp::getSum());
//			break;
//		case CARD:
//			set->setType(AggProp::getCard());
//			break;
//		case PROD:
//			set->setType(AggProp::getProd());
//			break;
//		default:
//			assert(false);
//	}
//}
//
//void MinToMax::transform(PCSolver* solver, TypedSet* set, bool& unsat, bool& sat) const {
//	if (set->getAgg()[0]->getType() == MIN) {
//		//Transform Min into Max set: invert all weights
//		vwl wl;
//		for (vsize i = 0; i < set->getWL().size(); ++i) {
//			wl.push_back(WL(set->getWL()[i].getLit(), -set->getWL()[i].getWeight()));
//		}
//		set->setWL(wl);
//
//		//Invert the bound of all the aggregates involved
//		for (agglist::const_iterator i = set->getAgg().begin(); i < set->getAgg().end(); ++i) {
//			Weight bound = -(*i)->getBound();
//			AggSign sign = (*i)->getSign()==AGGSIGN_LB?AGGSIGN_UB:AGGSIGN_LB;
//			(*i)->setBound(AggBound(sign, bound));
//			assert((*i)->getType()==MIN);
//			(*i)->setType(MAX);
//		}
//	}
//}
//
//
