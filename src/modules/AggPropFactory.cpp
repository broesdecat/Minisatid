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

const PCSolver& AggPropFactory::getPCSolver() const { return getPropagatorFactory().getEngine(); }
PCSolver& AggPropFactory::getPCSolver() { return getPropagatorFactory().getEngine(); }

bool 		AggPropFactory::hasIDSolver(int defid) const { return getPropagatorFactory().hasIDSolver(defid); }
IDSolver& 	AggPropFactory::getIDSolver(int defid) { return *getPropagatorFactory().getIDSolver(defid); }

AggPropFactory::AggPropFactory(PropagatorFactory* s) :
		propagatorfactory(s),
		dummyhead(-1){
}

AggPropFactory::~AggPropFactory() {
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

	if (parsedSets.find(setid) != parsedSets.end()) {
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

bool AggPropFactory::addAggExpr(const InnerNonReifAggregate& agg){
	//TODO
}

bool AggPropFactory::addAggrExpr(const InnerAggregate& agg){

template<class C, class Elem>
bool alreadyInContainer(const Elem& elem, const C& container){
	return container.end()==container.find(elem);
}

bool AggPropFactory::addAggrExpr(const InnerAggregate& agg, bool reified){
	if (!alreadyInContainer(agg.setID, parsedSets)) {
		throwUndefinedSet(agg.setID);
	}

	if (agg.head < 0) {
		throwNegativeHead(agg.head);
	}

	TypedSet* set = parsedSets[agg.setID];

	for (vwl::const_iterator i=set->getWL().begin(); i<set->getWL().end(); ++i) {
		if (var((*i).getLit()) == agg.head) {
			throwHeadOccursInSet(agg.head, agg.setID);
		}
	}

	//Check that no aggregates occur with the same heads
	if(alreadyInContainer(agg.head, heads)){
		if(reified){
			throwDuplicateHeads(agg.head);
		}else{
			 agg.head == dummyhead;
		}
	}

	//TODO
	/*
	heads.insert(agg.head);

#ifdef DEBUG
	if(agg.type == CARD) { //Check if all card weights are 1
		for(vwl::size_type i=0; i<parsedSets[agg.setID]->getWL().size(); ++i) {
			if(parsedSets[agg.setID]->getWL()[i].getWeight()!=1) {
				report("Cardinality was loaded with wrong weights");
				assert(false);
			}
		}
	}
#endif

	getPCSolver().varBumpActivity(agg.head);

	Lit head = mkLit(agg.head, false); //TODO Var!
	Agg* aggregate = new Agg(head, AggBound(agg.sign, agg.bound),agg.sem, agg.defID, agg.type);
	set->addAgg(aggregate);

	return true;
}

void AggPropFactory::finishParsing(bool& present, bool& unsat) {
	unsat = false;
	present = true;

	if (parsedSets.size() == 0) {
		present = false;
		notifyInitialized();
		return;
	}

	if(verbosity() >= 3){
		report("Initializing aggregates\n");
	}

	//IMPORTANT: LAZY initialization!
	adaptToNVars(nVars());

	for(mips::const_iterator i=parsedSets.begin(); i!=parsedSets.end(); ++i){
		sets.push_back((*i).second);
	}

	// Initialization of all sets

	//Rewrite completion sum and card constraints into CNF using PBSOLVER
	if(getPCSolver().modes().pbsolver && !unsat){
		unsat = !transformSumsToCNF(sets, *this);
	}

	//Finish the sets: add all body literals to the network
	vps remainingsets;
	vps satsets;
	for (vsize i=0; !unsat && i<sets.size(); ++i) {
		TypedSet* set = sets[i];
		bool setsat = false;

		if(!unsat && !setsat){
			//FIXME: error in new engine because watches are added before full initialization is done, sometimes leading to propagation calls before full initialization is done (which is not allowed!)
			set->initialize(unsat, setsat, sets);
		}

		if(!unsat && !setsat){
			for (vsize i = 0; i < set->getWL().size(); ++i) {
				var2setlist[var(set->getWL()[i].getLit())].push_back(set);
			}
		}

		if(setsat){
			satsets.push_back(set);
		}else{
			assert(unsat || set->getAgg().size()>0);
			remainingsets.push_back(set);
		}
	}
	sets.clear();
	sets.insert(sets.begin(), remainingsets.begin(), remainingsets.end());
	deleteList<TypedSet>(satsets);

#ifdef DEBUG
	//Check each aggregate knows it index in the set
	for(vps::const_iterator j=sets.begin(); j<sets.end(); ++j){
		for (agglist::const_iterator i = (*j)->getAgg().begin(); i<(*j)->getAgg().end(); ++i) {
			assert((*j)==(*i)->getSet());
			assert((*i)->getSet()->getAgg()[(*i)->getIndex()]==(*i));
		}
	}

	//TODO check all watches are correct
#endif

	if(unsat){
		if (verbosity() >= 3) {
			report("Initializing aggregates finished, unsat detected.\n");
		}
		notifyInitialized();
		return;
	}

	//Gather available information
	map<AggType, int> nbaggs;
	int totalagg = 0, setlits = 0;
	for (vps::const_iterator i = sets.begin(); i < sets.end(); ++i) {
		int agg = (*i)->getAgg().size();
		totalagg += agg;
		setlits += (*i)->getWL().size();
		nbaggs[(*i)->getType().getType()]+=agg; //Defaults to 0 if new: http://forums.whirlpool.net.au/archive/1286863
	}

	if (totalagg == 0) {
		if (verbosity() >= 3) {
			report("Initializing aggregates finished, no aggregates present after initialization.\n");
		}
		present = false;
		notifyInitialized();
		return;
	}*/
}

/*
bool printedwarning = false;

AggPropagator*	MaxProp::createPropagator(TypedSet* set) const{
	if(set->isUsingWatches() && !printedwarning){
		clog <<">> Currently max/min aggregates never use watched-literal-schemes.\n";
		printedwarning = true;
	}
	return new MaxFWAgg(set);
}

//Propagator*	MinProp::createPropagator(TypedSet* set) const{
//	if(set->isUsingWatches() && !printedwarning){
//		clog <<">> Currently max/min aggregates never use watched-literal-schemes.\n";
//		printedwarning = true;
//	}
//	return new MinFWAgg(set);
//}

AggPropagator*	SumProp::createPropagator(TypedSet* set) const{
	set->getSolver()->adaptAggHeur(set->getWL(), set->getAgg().size());

	if(set->isUsingWatches()){
		return new GenPWAgg(set);
	}else{
		return new SumFWAgg(set);
	}
}

AggPropagator*	ProdProp::createPropagator(TypedSet* set) const{
	set->getSolver()->adaptAggHeur(set->getWL(), set->getAgg().size());

	if(set->isUsingWatches()){
		return new GenPWAgg(set);
	}else{
		return new ProdFWAgg(set);
	}
}
*/
 */
