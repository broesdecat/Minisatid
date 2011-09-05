/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#include "modules/LazyGrounder.hpp"

using namespace std;
using namespace MinisatID;

LazyGrounder::LazyGrounder(){
}

LazyGrounder::~LazyGrounder() {
	deleteList<LazyGroundedClause>(clauses);
}

void LazyGrounder::addClause(const InnerDisjunction& clause){
	clauses.push_back(new LazyGroundedClause(clause));
}

bool LazyGrounder::expand(int clauseID, litlist& currentclause){
	LazyGroundedClause lz = *clauses[clauseID];
	if(lz.clause.literals.size()<=lz.indexofnext){
		return false;
	}
	currentclause.push_back(lz.clause.literals[lz.indexofnext++]);
	return true;
}
/*
bool LazyGrounder::setClause(const InnerDisjunction& clause){
	this->clause = clause;

	bool found = false;
	while(!found && indexinfullclause<clause.literals.size()){
		indexinfullclause++;
		if(!isFalse(clause.literals[indexinfullclause])){
			found = true;
			getPCSolver().acceptLitEvent(this, ~clause.literals[indexinfullclause], SLOW);
		}
	}
	if(!found){
		return false;
	}
	return true;
}

rClause	LazyGrounder::notifypropagate(){
	rClause confl = nullPtrClause;
	while(confl==nullPtrClause && hasNextProp()){
		const Lit& lit = getNextProp();
		int index = 0;
		bool found = false;
		while(!found && index<clause.literals.size()){
			if(indexinfullclause<index){
				indexinfullclause++;
			}
			if(!isFalse(clause.literals[index])){
				found = true;
				getPCSolver().acceptLitEvent(this, ~clause.literals[index], SLOW);
			}
			index++;
		}
		if(!found){
			//have seen full clause (finally), so conflict: return a clause and add a watch again
			//TODO should add the clause as a permanent one and refrain from adding the clause to the watches again
			getPCSolver().acceptLitEvent(this, ~lit, SLOW);
			confl = getPCSolver().createClause(clause.literals, true);
			getPCSolver().addLearnedClause(confl);
		}
	}
	return confl;
}

void LazyGrounder::printStatistics() const {
	clog <<"Lazy grounded: " <<(indexinfullclause+1) <<" of " <<clause.literals.size() <<" literals.\n";
}*/
