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
#include "iostream"

#include "satsolver/SATSolver.hpp"
#include "theorysolvers/PCSolver.hpp"
#include "modules/IDSolver.hpp"
#include "modules/ModSolver.hpp"
#include "theorysolvers/SOSolver.hpp"
#include "modules/AggSolver.hpp"

using namespace std;
using namespace MinisatID;
using namespace Print;
using namespace Minisat;


/*template<class S>
void Print::print(S const * const s){
	clog <<"Solver is present, but no printing information.\n");
}*/

template<>
void Print::print(PCSolver const * const s){
	print(s->getCSolver());
	for(vector<DPLLTSolver*>::const_iterator i=s->getSolversBegin(); i<s->getSolversEnd(); i++){
		(*i)->get()->print();
	}
}

template<>
void Print::print(AggSolver const * const p){
	if(p==NULL){
		clog <<"No aggregates\n";
		return;
	}
	clog <<"Aggregates\n";
	//TODO
}

template<>
void Print::print(Solver const * const s){
	assert(s!=NULL);
	clog <<"Clauses\n";
	for(int i=0; i< s->nbClauses(); i++){
		s->printClause(s->getClause(i));
		clog <<"\n";
	}
}

template<>
void Print::print(IDSolver const * const s){
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
			gprintLit(r.getHead());
			int counter = 0;
			while(counter<r.size()){
				gprintLit(r[counter]);
				counter++;
			}
			clog <<"\n");*/
		//}
	}
}

template<class C>
inline void Print::printClause(const C& c){
    for (int i = 0; i < c.size(); i++){
        gprintLit(c[i]);
        fprintf(stderr, " ");
    }
}

template<class S>
void Print::printClause(rClause c, S const * const s){
	s->printClause(getClauseRef(c));
}

template<>
void Print::printClause(rClause c, PCSolver const * const s){
	printClause(c, s->getCSolver());
}

template<>
void Print::print(ModSolver const * const m){
	clog <<"ModSolver " <<m->getPrintId() <<" parent " <<m->getParentPrintId();
	if(m->hasParent()){
		clog <<", head";
		gprintLit(mkLit(m->getHead()), m->getHeadValue());
	}
	clog <<", children ";
	for(vmodindex::const_iterator i=m->getChildren().begin(); i<m->getChildren().end(); i++){
		clog <<*i;
	}
	clog <<"\nModal atoms ";
	for(vector<Var>::const_iterator i=m->getAtoms().begin(); i<m->getAtoms().end(); i++){
		clog <<gprintVar(*i);
	}
	/*clog <<"\nsubtheory\n");
	print(m->getPCSolver());*/
	clog <<"SubSolvers\n";
	for(vmodindex::const_iterator i=m->getChildren().begin(); i<m->getChildren().end(); i++){
		print(m->getModSolverData().getModSolver(*i));
	}
}

template<>
void Print::print(SOSolver const * const d){
	clog <<"Printing theory\n";
	print(d->getModSolver((modindex)0));
	clog <<"End of theory\n";
}
