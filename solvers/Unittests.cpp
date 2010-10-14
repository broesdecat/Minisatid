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

#include "solvers/Unittests.hpp"

using namespace MinisatID;

shared_ptr<SolverInterface> unittest(ECNF_mode& modes){ //unsat
	modes.cp = true;
	shared_ptr<PropositionalSolver> pcsolver = shared_ptr<PropositionalSolver>(new PropositionalSolver(modes));
	vector<Literal> lits, lits2, lits3;
	lits.push_back(Literal(1));
	lits.push_back(Literal(2, true));
	lits.push_back(Literal(3));
	lits2.push_back(Literal(1));
	lits2.push_back(Literal(2));
	lits2.push_back(Literal(3));
	lits3.push_back(Literal(3, true));
	pcsolver->addClause(lits);
	pcsolver->addClause(lits2);
	pcsolver->addClause(lits3);
	int groundone=1, groundtwo=2;
	pcsolver->addIntVar(groundone, -3, 7);
	pcsolver->addIntVar(groundtwo, 7, 10);
	vector<int> terms;
	terms.push_back(groundone);
	terms.push_back(groundtwo);
	pcsolver->addCPSum(Literal(1), terms, MINISAT::MGEQ, 18);

	if(!pcsolver->finishParsing()){
		return shared_ptr<SolverInterface>();
	}

	return pcsolver;
}

//Magic sequence problem
shared_ptr<SolverInterface> unittest2(ECNF_mode& modes){
	modes.cp = true;
	shared_ptr<PropositionalSolver> pcsolver = shared_ptr<PropositionalSolver>(new PropositionalSolver(modes));
	vector<Literal> lits;
	lits.push_back(Literal(1));
	lits.push_back(Literal(2));
	lits.push_back(Literal(3));
	pcsolver->addClause(lits);
	vector<int> mult;
	vector<int> elemx;
	int n = 1000;
	for(int i=0; i<n; i++){
		mult.push_back(i-1);
		int x = i;
		pcsolver->addIntVar(x, 0, n);
		elemx.push_back(x);
	}

	for(int i=0; i<n; i++){
		pcsolver->addCPCount(elemx, i, MINISAT::MEQ, elemx[i]);
	}

	vector<Literal> lits2;
	lits2.push_back(Literal(4));
	pcsolver->addClause(lits2);
	pcsolver->addCPSum(Literal(4), elemx, MINISAT::MEQ, n);

	vector<Literal> lits3;
	lits3.push_back(Literal(5));
	pcsolver->addClause(lits3);
	pcsolver->addCPSum(Literal(5), elemx, mult, MINISAT::MEQ, 0);

	int literalcount = 6;
	for(int i=0; i<n; i++){
		for(int j=0; j<n; j++){
			pcsolver->addCPBinaryRel(Literal(literalcount++), elemx[i], MINISAT::MEQ, j);
			pcsolver->addCPBinaryRel(Literal(literalcount++), elemx[i], MINISAT::MGEQ, j);
		}
	}

	if(!pcsolver->finishParsing()){
		return shared_ptr<SolverInterface>();
	}

	return pcsolver;
}

shared_ptr<SolverInterface> unittest3(ECNF_mode& modes){ //unsat
	modes.cp = true;
	shared_ptr<PropositionalSolver> pcsolver = shared_ptr<PropositionalSolver>(new PropositionalSolver(modes));

	vector<int> elemx;
	int n = 4;
	for(int i=1; i<n; i++){
		pcsolver->addIntVar(i, 1, 2);
		elemx.push_back(i);
	}

	int c = 1;
	for(int i=0; i<elemx.size(); i++){
		int left = c;
		for(int j=0; j<elemx.size(); j++, c++){
			pcsolver->addCPBinaryRelVar(Literal(c), elemx[i], MINISAT::MNEQ, elemx[j]);
			if(i+j<n){
				vector<Literal> lits;
				lits.push_back(Literal(left));
				lits.push_back(Literal(c+i+1));
				pcsolver->addClause(lits);
			}
		}
	}

	if(!pcsolver->finishParsing()){
		return shared_ptr<SolverInterface>();
	}

	return pcsolver;
}
