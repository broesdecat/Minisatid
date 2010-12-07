//--------------------------------------------------------------------------------------------------
//    Copyright (c) 2009-2010, Broes De Cat, K.U.Leuven, Belgium
//    
//    Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
//    associated documentation files (the "Software"), to deal in the Software without restriction,
//    including without limitation the rights to use, copy, modify, merge, publish, distribute,
//    sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
//    furnished to do so, subject to the following conditions:
//    
//    The above copyright notice and this permission notice shall be included in all copies or
//    substantial portions of the Software.
//    
//    THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
//    NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
//    NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
//    DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
//    OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
//--------------------------------------------------------------------------------------------------

#include "solvers/utils/Print.hpp"

#include <vector>

#include "solvers/satsolver/SATSolver.h"
#include "solvers/theorysolvers/PCSolver.hpp"
#include "solvers/modules/IDSolver.hpp"
#include "solvers/modules/ModSolver.hpp"
#include "solvers/theorysolvers/SOSolver.hpp"
#include "solvers/modules/AggSolver.hpp"

using namespace std;
using namespace MinisatID;
using namespace Print;
using namespace Minisat;


/*template<class S>
void Print::print(S const * const s){
	report("Solver is present, but no printing information.\n");
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
		report("No aggregates\n");
		return;
	}
	report("Aggregates\n");
	//TODO
}

template<>
void Print::print(Solver const * const s){
	assert(s!=NULL);
	report("Clauses\n");
	for(int i=0; i< s->nbClauses(); i++){
		s->printClause(s->getClause(i));
		report("\n");
	}
}

template<>
void Print::print(IDSolver const * const s){
	if(s==NULL){
		report("No definitions\n");
		return;
	}
	report("Definitions\n");
	for(int i=0; i<s->nVars(); i++){
		//if(s->isDefined(i)){
			/*DefType d = s->getDefType(i);
			if(s->isConjunctive(i)){
				report("Conjunctive rule");
			}else if(s->isDisjunctive(i)){
				report("Disjunctive rule");
			}else if(s->isDefinedByAggr(i)){
				report("Aggregate rule");
			}*/

			/*FIXME const PropRule& r = *s->getDefinition(i);
			gprintLit(r.getHead());
			int counter = 0;
			while(counter<r.size()){
				gprintLit(r[counter]);
				counter++;
			}
			report("\n");*/
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
	report("ModSolver %zu, parent %zu", m->getPrintId(), m->getParentPrintId() );
	if(m->hasParent()){
		report(", head");
		gprintLit(mkLit(m->getHead()), m->getHeadValue());
	}
	report(", children ");
	for(vmodindex::const_iterator i=m->getChildren().begin(); i<m->getChildren().end(); i++){
		report("%zu ", *i);
	}
	report("\nModal atoms ");
	for(vector<Var>::const_iterator i=m->getAtoms().begin(); i<m->getAtoms().end(); i++){
		report("%d ", gprintVar(*i));
	}
	/*report("\nsubtheory\n");
	print(m->getPCSolver());*/
	report("SubSolvers\n");
	for(vmodindex::const_iterator i=m->getChildren().begin(); i<m->getChildren().end(); i++){
		print(m->getModSolverData().getModSolver(*i));
	}
}

template<>
void Print::print(SOSolver const * const d){
	report("Printing theory\n");
	print(d->getModSolver((modindex)0));
	report("End of theory\n");
}
