/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#include "modules/aggsolver/AggPrint.hpp"

#include "modules/aggsolver/AggSet.hpp"
#include "modules/aggsolver/PartiallyWatched.hpp"

#include "utils/Print.hpp"

using namespace std;
using namespace MinisatID;

template<class T>
void printValue(T& output, lbool value){
	output <<"(" <<(value==l_Undef?"U":value==l_True?"T":"F") <<")";
}

void MinisatID::print(int verbosity, const TypedSet& c, bool endl) {
	if(verbosity<5){
		clog <<"set " <<c.getSetID();
	}else{
		clog <<"set " <<c.getSetID() <<" = {";
		bool begin = true;
		for (auto i = c.getWL().cbegin(); i < c.getWL().cend(); ++i) {
			if(!begin){
				clog <<", ";
			}
			begin = false;
			clog <<c.toString((*i).getLit());
			clog <<"=" <<(*i).getWeight();
		}
		clog <<" }";
	}
	if (endl) {
		clog <<"\n";
	}
}

void MinisatID::print(int verbosity, const Agg& ae, bool endl) {
	clog <<toString(ae.getHead(), ae.getSet()->getPCSolver());
	lbool value = ae.getSet()->value(ae.getHead());
	printValue(clog, value);
	TypedSet* set = ae.getSet();
	switch(ae.getSem()){
		case AggSem::DEF:
			clog <<"<- ";
			break;
		case AggSem::COMP:
			clog <<"<=> ";
			break;
		case AggSem::OR:
			clog <<"| ";
			break;
	}
	if (ae.hasLB()) {
		clog <<ae.getBound() <<" =< ";
	}
	clog <<ae.getType() <<"{";
	print(verbosity, *set, false);
	clog <<"}";
	if (ae.hasUB()) {
		clog <<" =< " <<ae.getBound();
	}
	clog <<".";
	if(endl){
		clog <<"\n";
	}
}
