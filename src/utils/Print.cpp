//------------------------------------------------------------------------------
// Copyright (c) 2009, 2010, 2011, Broes De Cat, K.U. Leuven, Belgium
//
// This file is part of MinisatID.
//
// MinisatID is free software: you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// MinisatID is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with MinisatID. If not, see <http://www.gnu.org/licenses/>.
//------------------------------------------------------------------------------

#include "utils/Print.hpp"

#include <vector>
#include <iostream>

#include "satsolver/SATSolver.hpp"

#include "theorysolvers/PCSolver.hpp"
#include "theorysolvers/SOSolver.hpp"

#include "modules/IDSolver.hpp"
#include "modules/ModSolver.hpp"
#include "modules/AggSolver.hpp"

using namespace std;
using namespace MinisatID;
using namespace Minisat;

namespace MinisatID{

namespace Print{

int getPrintableVar(Var v){
	return v+1;
}

template<>
void print(const Minisat::Lit& lit, const lbool val){
	std::clog <<(sign(lit)?"-":"") <<getPrintableVar(var(lit)) <<":" <<(val==l_True?'1':(val==l_False?'0':'X'));
}

template<>
void print(const Minisat::Lit& lit){
	std::clog <<(sign(lit)?"-":"") <<getPrintableVar(var(lit));
}

template<>
void print(const Minisat::vec<Minisat::Lit>& v){
	for(int i=0; i<v.size(); i++) {
		if(i<v.size()-1){
			clog <<" ";
		}
		print(v[i]);
	}
	clog <<"\n";
}

template<>
void print(Solver const * const s){
	assert(s!=NULL);
	clog <<"Clauses\n";
	for(int i=0; i< s->nbClauses(); i++){
		s->printClause(s->getClause(i));
		clog <<"\n";
	}
}

template<>
void print(PCSolver * const s){
	print(s->getCSolver());
	for(vector<DPLLTSolver*>::const_iterator i=s->getSolversBegin(); i<s->getSolversEnd(); i++){
		(*i)->get()->print();
	}
}

template<>
void print(AggSolver const * const p){
	if(p==NULL){
		clog <<"No aggregates\n";
		return;
	}
	clog <<"Aggregates\n";
	//TODO
}

template<>
void print(IDSolver const * const s){
	if(s==NULL){
		clog <<"No definitions\n";
		return;
	}
	clog <<"Definitions\n";
	for(int i=0; i<s->nVars(); i++){
		//if(s->isDefined(i)){
			/*DefType d = s->getDefType(i);
			if(s->isConjunctive(i)){
				clog <<"Conjunctive rule");
			}else if(s->isDisjunctive(i)){
				clog <<"Disjunctive rule");
			}else if(s->isDefinedByAggr(i)){
				clog <<"Aggregate rule");
			}*/

			/*FIXME const PropRule& r = *s->getDefinition(i);
			print(r.getHead());
			int counter = 0;
			while(counter<r.size()){
				print(r[counter]);
				counter++;
			}
			clog <<"\n");*/
		//}
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
	for(vmodindex::const_iterator i=m->getChildren().begin(); i<m->getChildren().end(); i++){
		clog <<*i;
	}
	clog <<"\nModal atoms ";
	for(vector<Var>::const_iterator i=m->getAtoms().begin(); i<m->getAtoms().end(); i++){
		clog <<getPrintableVar(*i);
	}
	/*clog <<"\nsubtheory\n");
	print(m->getPCSolver());*/
	clog <<"SubSolvers\n";
	for(vmodindex::const_iterator i=m->getChildren().begin(); i<m->getChildren().end(); i++){
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
	for(vmodindex::const_iterator i=m->getChildren().begin(); i<m->getChildren().end(); i++){
		clog <<*i;
	}
	clog <<"\nModal atoms ";
	for(vector<Var>::const_iterator i=m->getAtoms().begin(); i<m->getAtoms().end(); i++){
		clog <<getPrintableVar(*i);
	}
	/*clog <<"\nsubtheory\n");
	print(m->getPCSolver());*/
	clog <<"SubSolvers\n";
	for(vmodindex::const_iterator i=m->getChildren().begin(); i<m->getChildren().end(); i++){
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
void print(rClause c, S * const s){
	s->printClause(getClauseRef(c));
}

template<>
void print(rClause c, PCSolver * const s){
	print(c, s->getCSolver());
}

}

}
