/*
 * LazyGrounder.cpp
 *
 *  Created on: May 30, 2011
 *      Author: broes
 */

#include "modules/LazyGrounder.hpp"

#include "theorysolvers/PCSolver.hpp"

using namespace std;
using namespace MinisatID;

LazyGrounder::LazyGrounder(PCSolver* pcsolver): Propagator(pcsolver) {

}

LazyGrounder::~LazyGrounder() {
}

bool LazyGrounder::setClause(const InnerDisjunction& clause){
	this->clause = clause;

	bool found = false;
	while(!found && indexinfullclause<clause.literals.size()){
		indexinfullclause++;
		if(!isFalse(clause.literals[indexinfullclause])){
			found = true;
			getPCSolver().acceptVarEvent(this, var(clause.literals[indexinfullclause]));
		}
	}
	if(!found){
		return false;
	}
	return true;
}

rClause	LazyGrounder::notifypropagate(){
	rClause confl;
	while(confl==nullPtrClause && hasNextProp()){
		const Lit& lit = getNextProp();
		int index = 0;
		bool found = false;
		while(!found && index<clause.literals.size()){
			index++;
			if(indexinfullclause<index){
				indexinfullclause++;
			}
			if(!isFalse(clause.literals[index])){
				found = true;
				getPCSolver().acceptVarEvent(this, var(clause.literals[index]));
			}
		}
		if(!found){
			//have seen full clause (finally), so conflict: return a clause and add a watch again
			//TODO should add the clause as a permanent one and refrain from adding the clause to the watches again
			getPCSolver().acceptVarEvent(this, var(lit));
			confl = getPCSolver().createClause(clause.literals, true);
			getPCSolver().addLearnedClause(confl);
		}
	}
	return nullPtrClause;
}
