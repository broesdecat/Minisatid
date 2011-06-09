/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#include "modules/AggPropFactory.hpp"

#include <sstream>

#include "utils/Utils.hpp"
#include "theorysolvers/PCSolver.hpp"
#include "modules/IDSolver.hpp"

#include "modules/aggsolver/AggUtils.hpp"
#include "modules/aggsolver/AggTransform.hpp"

#include "modules/aggsolver/FullyWatched.hpp"
#include "modules/aggsolver/PartiallyWatched.hpp"

#include "utils/Print.hpp"

using namespace std;
using namespace MinisatID;

const PCSolver& AggPropFactory::getEngine() const { return getPropagatorFactory().getEngine(); }
PCSolver& AggPropFactory::getEngine() { return getPropagatorFactory().getEngine(); }
PCSolver* AggPropFactory::getEnginep() { return getPropagatorFactory().getEnginep(); }

bool 		AggPropFactory::hasIDSolver(int defid) const { return getPropagatorFactory().hasIDSolver(defid); }
IDSolver& 	AggPropFactory::getIDSolver(int defid) { return *getPropagatorFactory().getIDSolver(defid); }

AggPropFactory::AggPropFactory(PropagatorFactory* s) :
		propagatorfactory(s),
		temphead(-1), dummyhead(-1){
}

AggPropFactory::~AggPropFactory() {
	deleteList<TypedSet>(sets);
}

void throwUndefinedSet(int setid){
	stringstream ss;
	ss <<"Set nr. " <<setid <<" is used, but not defined yet.\n";
	throw idpexception(ss.str());
}

void throwDoubleDefinedSet(int setid){
	stringstream ss;
	ss <<"Set nr. " <<setid <<" is defined more than once.\n";
	throw idpexception(ss.str());
}

void throwEmptySet(int setid){
	stringstream ss;
	ss <<"Set nr. " <<setid <<" is empty.\n";
	throw idpexception(ss.str());
}

void throwNegativeHead(Var head){
	stringstream ss;
	ss <<"An aggregate cannot be defined by a negative head, violated for " <<getPrintableVar(head) <<".\n";
	throw idpexception(ss.str());
}

void throwHeadOccursInSet(Var head, int setid){
	stringstream ss;
	ss <<"For the aggregated with head " <<getPrintableVar(head) <<" also occurs in its set.\n";
	throw idpexception(ss.str());
}

void throwDuplicateHeads(Var head){
	strinstream ss;
	ss <<"Multiple aggregates with the same heads " <<getPrintableVar(head) <<".\n";
	throw idpexception(ss.str());
}

bool AggPropFactory::addSet(int setid, const vector<WL>& weightedlits) {
	if (weightedlits.size() == 0) {
		throwEmptySet(setid);
	}

	if (alreadyInContainer(setid, parsedSets)) {
		throwDoubleDefinedSet(setid);
	}

	for (vwl::const_iterator i=weightedlits.begin(); i<weightedlits.end(); ++i) {
#ifdef NOARBITPREC
		if((*i).getWeight() == posInfinity() || (*i).getWeight() == negInfinity()){
			throw idpexception("Weights cannot equal the largest or smallest integer in limited precision. Recompile with GMP.\n");
		}
#endif
	}

	TypedSet* set = new TypedSet(setid);
	set->setWL(weightedlits);
	parsedSets[setid] = set;

	return true;
}

bool AggPropFactory::addAggrExpr(const InnerReifAggregate& agg){
	if(alreadyInContainer(agg.head, heads)){
		throwDuplicateHeads(agg.head);
	}
	return addAggr(agg);
}

bool AggPropFactory::addAggrExpr(const InnerAggregate& agg){
	InnerReifAggregate newagg;
	newagg.head = temphead;
	newagg.bound = agg.bound;
	newagg.sem = COMP; //TODO can also be implication if only one model / sat equivalence is needed
	newagg.setID = agg.setID;
	newagg.type = agg.type;
	return addAggr(newagg);
}

template<class C, class Elem>
bool alreadyInContainer(const Elem& elem, const C& container){
	return container.end()==container.find(elem);
}

bool AggPropFactory::addAggrExpr(const InnerReifAggregate& agg){
	if (!alreadyInContainer(agg.setID, parsedSets)) {
		throwUndefinedSet(agg.setID);
	}

	TypedSet* set = parsedSets[agg.setID];
	heads.insert(agg.head);

	Lit head = mkLit(agg.head, false);
	Agg* aggregate = new Agg(head, AggBound(agg.sign, agg.bound),agg.sem, agg.defID, agg.type);
	set->addAgg(aggregate);

	for (vwl::const_iterator i=set->getWL().begin(); i<set->getWL().end(); ++i) {
		if (var((*i).getLit()) == agg.head) {
			throwHeadOccursInSet(agg.head, agg.setID);
		}
#ifdef DEBUG
		if(agg.type == CARD) {
			assert((*i).getWeight()==1);
		}
#endif
	}

	return true;
}

void AggPropFactory::initializeAllSets(){
	setlist remainingsets;
	setlist satsets;
	for (setlist::iterator i=sets.begin(); !unsat && i<sets.end(); ++i) {
		TypedSet* set = *i;

		for(agglist::iterator j=set->getAggNonConst().begin(); j<set->getAggNonConst().end(); ++h){
			if((*j)->getHead()==temphead){
				(*j)->setHead(dummyhead);
			}

			getEngine().varBumpActivity((*j)->getHead());
		}

		bool removeset = false;
		if(!unsat && !removeset){
			set->initialize(unsat, removeset, sets);
		}

		if(removeset){
			satsets.push_back(set);
		}else{
			assert(unsat || set->getAgg().size()>0);
			remainingsets.push_back(set);
		}
	}
	sets.clear();
	sets.insert(sets.begin(), remainingsets.begin(), remainingsets.end());
}

bool printedwarning = false;
void AggPropFactory::finishParsing(bool& unsat) {
	unsat = false;

	if (parsedSets.size() == 0) {
		return;
	}

	for(mips::const_iterator i=parsedSets.begin(); i!=parsedSets.end(); ++i){
		sets.push_back((*i).second);
	}

	// Initialization of all sets
	if(getEngine().modes().pbsolver && !unsat){
		unsat = !transformSumsToCNF(sets, getEngine());
	}

	dummyhead = mkLit(getEngine().newVar());
	InnerDisjunction unitclause;
	unitclause.literals.push(dummyhead);
	getEngine().add(unitclause);

	initializeAllSets();



	for(setlist::const_iterator i=remainingsets.begin(); i<remainingsets.end(); ++i){
		TypedSet* set = *i;
		sets.push_back(set);

		switch((*i)->type){
		case CARD:
		case SUM:
			if(set->isUsingWatches()){
				new GenPWAgg(getEnginep(), set);
			}else{
				new SumFWAgg(getEnginep(), set);
			}
			break;
		case PROD:
			if(set->isUsingWatches()){
				new GenPWAgg(getEnginep(), set);
			}else{
				new ProdFWAgg(getEnginep(), set);
			}
			break;
		case MAX:
			if(set->isUsingWatches() && !printedwarning){
				clog <<">> Currently max/min aggregates never use watched-literal-schemes.\n";
				printedwarning = true;
			}
			new MaxFWAgg(getEnginep(), set);
			break;
		default:
			assert(false);
		}
	}
	deleteList<TypedSet>(satsets);

#ifdef DEBUG
	//Check each aggregate knows it index in the set
	for(vps::const_iterator j=sets.begin(); j<sets.end(); ++j){
		for (agglist::const_iterator i = (*j)->getAgg().begin(); i<(*j)->getAgg().end(); ++i) {
			assert((*j)==(*i)->getSet());
			assert((*i)->getSet()->getAgg()[(*i)->getIndex()]==(*i));
		}
	}
#endif
}
