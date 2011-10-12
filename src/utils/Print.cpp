/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#include "utils/Print.hpp"

#include <vector>
#include <iostream>

#include "satsolver/SATSolver.hpp"

#include "theorysolvers/PCSolver.hpp"
#include "theorysolvers/SOSolver.hpp"

#include "modules/IDSolver.hpp"
#include "modules/ModSolver.hpp"

using namespace std;
using namespace MinisatID;

namespace MinisatID{

template<>
void print(const Minisat::Lit& lit, const lbool val){
	std::clog <<(sign(lit)?"-":"") <<getPrintableVar(var(lit)) <<":" <<(val==l_True?'1':(val==l_False?'0':'X'));
}

template<>
std::string print(const litlist& v){
	stringstream ss;
	bool begin = false;
	for(auto litit=v.cbegin(); litit<v.cend(); ++litit){
		if(not begin){
			ss <<" ";
		}
		begin = false;
		ss <<*litit;
	}
	ss <<"\n";
	return ss.str();
}

template<>
std::string print(const InnerDisjunction& clause){
	return print(clause.literals);
}

template<> std::string print(const Lit& lit){
	std::stringstream ss;
	ss <<(sign(lit)?"-":"") <<getPrintableVar(var(lit));
	return ss.str();
}

void print(const Minisat::Solver& s){
	clog <<"Clauses\n";
	for(int i=0; i< s.nbClauses(); ++i){
		s.printClause(s.getClause(i));
		clog <<"\n";
	}
}

template<>
void print(Minisat::Solver * const s){
	assert(s!=NULL);
	print(*s);
}

template<>
void print(Minisat::Solver const * const s){
	assert(s!=NULL);
	print(*s);
}

template<>
void print(PCSolver * const s){
	s->printState();
}

template<>
void print(IDSolver const * const s){
	if(s==NULL){
		clog <<"No definitions\n";
		return;
	}
	clog <<"Definitions\n";
	for(int i=0; i<s->nVars(); ++i){
		if(not s->isDefined(i)){
			continue;
		}
		if(s->isConjunctive(i)){
			clog <<"Conjunctive rule";
		}else if(s->isDisjunctive(i)){
			clog <<"Disjunctive rule";
		}else if(s->isDefinedByAggr(i)){
			clog <<"Aggregate rule";
		}

		const PropRule& r = s->getDefinition(i);
		clog <<r.getHead();
		int counter = 0;
		while(counter<r.size()){
			clog <<r[counter];
			++counter;
		}
		clog <<"\n";
	}
}

template<>
void print(ModSolver * const m){
	clog <<"ModSolver " <<m->getPrintId() <<" parent " <<m->getParentPrintId();
	if(m->hasParent()){
		clog <<", head";
		print(mkLit(m->getHead()), m->getHeadValue());
	}
	clog <<", children ";
	for(auto i=m->getChildren().cbegin(); i<m->getChildren().cend(); ++i){
		clog <<*i;
	}
	clog <<"\nModal atoms ";
	for(auto i=m->getAtoms().cbegin(); i<m->getAtoms().cend(); ++i){
		clog <<getPrintableVar(*i);
	}
	/*clog <<"\nsubtheory\n");
	print(m->getPCSolver());*/
	clog <<"SubSolvers\n";
	for(auto i=m->getChildren().cbegin(); i<m->getChildren().cend(); ++i){
		print(m->getModSolverData().getModSolver(*i));
	}
}

template<>
void print(ModSolver const * const m){
	clog <<"ModSolver " <<m->getPrintId() <<" parent " <<m->getParentPrintId();
	if(m->hasParent()){
		clog <<", head";
		print(mkLit(m->getHead()), m->getHeadValue());
	}
	clog <<", children ";
	for(auto i=m->getChildren().cbegin(); i<m->getChildren().cend(); ++i){
		clog <<*i;
	}
	clog <<"\nModal atoms ";
	for(auto i=m->getAtoms().cbegin(); i<m->getAtoms().cend(); ++i){
		clog <<getPrintableVar(*i);
	}
	/*clog <<"\nsubtheory\n");
	print(m->getPCSolver());*/
	clog <<"SubSolvers\n";
	for(auto i=m->getChildren().cbegin(); i<m->getChildren().cend(); ++i){
		print(m->getModSolverData().getModSolver(*i));
	}
}

template<>
void print(SOSolver * const d){
	clog <<"Printing theory\n";
	print(d->getModSolver((modindex)0));
	clog <<"End of theory\n";
}

template<>
void print(SOSolver const * const d){
	clog <<"Printing theory\n";
	print(d->getModSolver((modindex)0));
	clog <<"End of theory\n";
}


template<class S>
void print(rClause c, const S& s){
	s.printClause(getClauseRef(c));
}

template<>
void print(rClause c, const PCSolver& s){
	s.printClause(c);
}

}
