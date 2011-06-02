/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#include "modules/aggsolver/AggPrint.hpp"

#include "modules/aggsolver/AggProp.hpp"
#include "modules/aggsolver/PartiallyWatched.hpp"
#include "modules/AggSolver.hpp"

#include "utils/Print.hpp"

using namespace std;
using namespace MinisatID;

void MinisatID::setAdded(){

}

void MinisatID::aggrAdded(){

}

void MinisatID::litPropagated(){

}

void MinisatID::explanationGenerated(){

}

void MinisatID::sets(){

}

void MinisatID::printWatches(int verbosity, AggSolver const * const solver, const std::vector<std::vector<Watch*> >& tempwatches){
	if(verbosity<10){
		return;
	}
	clog <<"Current effective watches: \n";
	Var var = 0;
	for(vector<std::vector<Watch*> >::const_iterator i=tempwatches.begin(); i<tempwatches.end(); ++i, ++var){
		bool found = false;
		for(vsize j=0; !found && j<(*i).size(); ++j){
			for(vsize k=0; !found && k<(*i)[j]->getSet()->getAgg().size(); ++k){
				GenPWatch* watch2 = dynamic_cast<GenPWatch*>((*i)[j]);
				if(watch2!=NULL && watch2->isInWS()){
					found = true;
				}
			}
		}

		if(!found){
			continue;
		}

		clog<<"    Watch " <<toLit(2*var) <<" used by: \n";
		for(vsize j=0; j<(*i).size(); ++j){
			for(vsize k=0; k<(*i)[j]->getSet()->getAgg().size(); ++k){
				GenPWatch* watch2 = dynamic_cast<GenPWatch*>((*i)[j]);
				if(watch2!=NULL && watch2->isInWS()){
					clog<<"        ";
					print(verbosity, *(*i)[j]->getSet()->getAgg()[k], true);
				}
			}
		}
	}
	clog <<"\n";
}

template<class T>
void printValue(T& output, lbool value){
	output <<"(" <<(value==l_Undef?"X":value==l_True?"T":"F") <<")";
}

void MinisatID::print(int verbosity, const TypedSet& c, bool endl) {
	if(verbosity<7){
		clog <<"set " <<c.getSetID();
	}else{
		clog <<"set " <<c.getSetID() <<" = {";
		bool begin = true;
		for (vwl::const_iterator i = c.getWL().begin(); i < c.getWL().end(); ++i) {
			if(!begin){
				clog <<", ";
			}
			begin = false;
			clog <<(*i).getLit();
			lbool value = c.getSolver()->value((*i).getLit());
			printValue(clog, value);
			clog <<"=" <<(*i).getWeight();
		}
		clog <<" }, KB=" <<c.getKnownBound();
	}
	if (endl) {
		clog <<"\n";
	}
}

void MinisatID::print(int verbosity, const Agg& ae, bool endl) {
	clog <<ae.getHead();
	lbool value = ae.getSet()->getSolver()->value(ae.getHead());
	printValue(clog, value);
	TypedSet* set = ae.getSet();
	switch(ae.getSem()){
		case DEF:
			clog <<"<- ";
			break;
		case COMP:
			clog <<"<=> ";
			break;
		case IMPLICATION:
			clog <<"| ";
			break;
	}
	if (ae.hasLB()) {
		clog <<ae.getCertainBound() <<" <= ";
	}
	clog <<(ae.getType()==MAX?"MAX":ae.getType()==MIN?"MIN":ae.getType()==SUM?"SUM":ae.getType()==CARD?"CARD":"PROD") <<"{";
	print(verbosity, *set, false);
	clog <<"}";
	if (ae.hasUB()) {
		clog <<" <= " <<ae.getCertainBound();
	}
	clog <<".";
	if(endl){
		clog <<"\n";
	}
}
