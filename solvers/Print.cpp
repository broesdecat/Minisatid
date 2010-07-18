/*
 * Print.cpp
 *
 *  Created on: Jun 28, 2010
 *      Author: broes
 */

#include "solvers/Print.hpp"

namespace Print {

template<class S>
void print(S const * const s){
	reportf("Solver is present, but no printing information.\n");
}

template<>
void print(PCSolver const * const s){
	print(s->getCSolver());
	print(s->getCAggSolver());
	print(s->getCIDSolver());
	print(s->getCCPSolver());
}

template<>
void print(CP::CPSolver const * const p){
	if(p==NULL){
		reportf("No CP constraints\n");
		return;
	}
	reportf("CP constraints\n");
	//TODO
}

template<>
void print(AggSolver const * const p){
	if(p==NULL){
		reportf("No aggregates\n");
		return;
	}
	reportf("Aggregates\n");
	//TODO
}

template<>
void print(Solver const * const s){
	assert(s!=NULL);
	reportf("Clauses\n");
	for(int i=0; i< s->clauses.size(); i++){
		s->printClause(*s->clauses[i]);
		reportf("\n");
	}
}

template<>
void print(IDSolver const * const s){
	if(s==NULL){
		reportf("No definitions\n");
		return;
	}
	reportf("Definitions\n");
	for(int i=0; i<s->getNbDefinitions(); i++){
		if(s->getDefinition(i)!=NULL){
			DefType d = s->getDefType(i);
			if(d==CONJ || d==DISJ){
				reportf("%sRule", d==CONJ?"C":"D");
				const PropRule& r = *s->getDefinition(i);
				gprintLit(r.getHeadLiteral());
				int counter = 0;
				while(counter<r.size()){
					gprintLit(r[counter]);
					counter++;
				}
				reportf("\n");
			}
		}
	}
}

template<class C>
inline void printClause(const C& c){
    for (int i = 0; i < c.size(); i++){
        gprintLit(c[i]);
        fprintf(stderr, " ");
    }
}

template<class C, class S>
void printClause(const C& c, S const * const s){
	s->printClause(c);
}

template<>
void printClause(const Clause& c, PCSolver const * const s){
	printClause(c, s->getCSolver());
}

template<>
void print(ModSolver const * const m){
	reportf("ModSolver %zu, parent %zu", m->getPrintId(), m->getParentPrintId() );
	if(m->hasParent()){
		reportf(", head");
		gprintLit(Lit(m->getHead()), m->getHeadValue());
	}
	reportf(", children ");
	for(vmodindex::const_iterator i=m->getChildren().begin(); i<m->getChildren().end(); i++){
		reportf("%zu ", *i);
	}
	reportf("\nModal atoms ");
	for(vector<Var>::const_iterator i=m->getAtoms().begin(); i<m->getAtoms().end(); i++){
		reportf("%d ", gprintVar(*i));
	}
	reportf("\nsubtheory\n");
	print(m->getCPCSolver());
	reportf("SubSolvers\n");
	for(vmodindex::const_iterator i=m->getChildren().begin(); i<m->getChildren().end(); i++){
		print(m->getModSolverData().getModSolver(*i));
	}
}

template<>
void print(ModSolverData const * const d){
	reportf("Printing theory\n");
	print(d->getModSolver((modindex)0));
	reportf("End of theory\n");
}

}
