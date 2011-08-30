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

LazyClausePropagator::LazyClausePropagator(PCSolver* engine, const InnerLazyClause& lz):
		Propagator(engine),
		certainlytrue(false),
		head(lz.tseitin),
		monitor(lz.monitor){
	monitor->notifyClauseCreated(new LazyClauseRef(this));
	clause.literals.push_back(lz.first);
	getPCSolver().accept(this, lz.tseitin, SLOW);
	getPCSolver().accept(this, not lz.tseitin, SLOW);
	getPCSolver().accept(this, not lz.first, SLOW); // FIXME dynamic watches and 2-watched scheme
}

LazyClausePropagator::~LazyClausePropagator(){

}

void LazyClausePropagator::add(const Lit& lit){
	clause.literals.push_back(lit);
	getPCSolver().accept(this, not lit, SLOW);

	InnerDisjunction disj;
	disj.literals.push_back(not lit);
	disj.literals.push_back(head);
	getPCSolver().add(disj);
}

void LazyClausePropagator::handleFullyGround(){
	InnerDisjunction fullclause;
	fullclause.literals.push_back(not head);
	for(auto litit=clause.literals.begin(); litit<clause.literals.end(); ++litit){
		fullclause.literals.push_back(*litit);
	}

	getPCSolver().add(fullclause);
}

rClause LazyClausePropagator::notifypropagate(){
	if(certainlytrue){ // TODO the propagator should be removed then
		return nullPtrClause;
	}

	lbool headvalue = value(head);

	if(headvalue==l_False){
		bool fullyground = false;
		while(not fullyground){
			fullyground = monitor->requestMoreGrounding();
			if(getPCSolver().isUnsat()){
				return nullPtrClause;
			}
		}
		handleFullyGround();
		return nullPtrClause;
	}

	bool allFalse = true;
	bool oneTrue = false;
	for(auto litit=clause.literals.begin(); allFalse && litit<clause.literals.end(); ++litit){
		lbool litvalue = value(*litit);
		if(litvalue!=l_False){
			allFalse = false;
			if(litvalue==l_True){
				oneTrue = true;
			}
		}
	}

	if(headvalue==l_True){
		while(allFalse){
			bool fullyground = monitor->requestMoreGrounding();
			if(fullyground){
				handleFullyGround();
				return nullPtrClause;
			}
			if(getPCSolver().isUnsat()){
				return nullPtrClause;
			}
			lbool litvalue = value(clause.literals.back());
			if(litvalue!=l_False){
				allFalse = false;
			}
		}
	}else if(headvalue==l_Undef){
		if(oneTrue){
			getPCSolver().setTrue(head, this, nullPtrClause);
		}
	}

	return nullPtrClause;
}

void LazyClausePropagator::notifyCertainlyTrue(){
	certainlytrue = true;
}
void LazyClausePropagator::notifyCertainlyFalse(){
	getPCSolver().notifyUnsat();
}
