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

#include "modules/IDSolver.hpp"

using namespace std;
using namespace MinisatID;

namespace MinisatID{

template<>
void print(const Minisat::Lit& lit, const lbool val){
	std::clog <<(sign(lit)?"-":"") <<var(lit)+1 <<":" <<(val==l_True?'1':(val==l_False?'0':'X'));
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
	ss <<(sign(lit)?"-":"") <<var(lit)+1;
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
		const PropRule& r = s->getDefinition(i);
		clog <<r.getHead() <<" <- ";
		if(s->isConjunctive(i)){
			printList(r, " & ");
		}else if(s->isDisjunctive(i)){
			printList(r, " | ");
		}else if(s->isDefinedByAggr(i)){
			clog <<"aggregate rule"; // TODO print aggregate
		}
		clog <<"\n";
	}
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
