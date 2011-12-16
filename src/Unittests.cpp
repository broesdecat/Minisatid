/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#include "Unittests.hpp"

using namespace std;
using namespace MinisatID;


shared_ptr<WrappedLogicSolver> unittest(SolverOption& modes){ //unsat
	shared_ptr<WrappedPCSolver> pcsolver = shared_ptr<WrappedPCSolver>(new WrappedPCSolver(modes));
	/*vector<Literal> lits, lits2, lits3;
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
	pcsolver->addCPSum(Literal(1), terms, MGEQ, 18);*/

	return pcsolver;
}

//Magic sequence problem
shared_ptr<WrappedLogicSolver> unittest2(SolverOption& modes){
	shared_ptr<WrappedPCSolver> pcsolver = shared_ptr<WrappedPCSolver>(new WrappedPCSolver(modes));
	/*vector<Literal> lits;
	lits.push_back(Literal(1));
	lits.push_back(Literal(2));
	lits.push_back(Literal(3));
	pcsolver->addClause(lits);
	vector<int> mult;
	vector<int> elemx;
	int n = 1000;
	for(int i=0; i<n; ++i){
		mult.push_back(i-1);
		int x = i;
		pcsolver->addIntVar(x, 0, n);
		elemx.push_back(x);
	}

	for(int i=0; i<n; ++i){
		pcsolver->addCPCount(elemx, i, MEQ, elemx[i]);
	}

	vector<Literal> lits2;
	lits2.push_back(Literal(4));
	pcsolver->addClause(lits2);
	pcsolver->addCPSum(Literal(4), elemx, MEQ, n);

	vector<Literal> lits3;
	lits3.push_back(Literal(5));
	pcsolver->addClause(lits3);
	pcsolver->addCPSum(Literal(5), elemx, mult, MEQ, 0);

	int literalcount = 6;
	for(int i=0; i<n; ++i){
		for(int j=0; j<n; ++j){
			pcsolver->addCPBinaryRel(Literal(literalcount++), elemx[i], MEQ, j);
			pcsolver->addCPBinaryRel(Literal(literalcount++), elemx[i], MGEQ, j);
		}
	}*/

	return pcsolver;
}

shared_ptr<WrappedLogicSolver> unittest3(SolverOption& modes){ //unsat
	shared_ptr<WrappedPCSolver> pcsolver = shared_ptr<WrappedPCSolver>(new WrappedPCSolver(modes));

	/*vector<int> elemx;
	int n = 4;
	for(int i=1; i<n; ++i){
		pcsolver->addIntVar(i, 1, 2);
		elemx.push_back(i);
	}

	int c = 1;
	for(int i=0; i<elemx.size(); ++i){
		int left = c;
		for(int j=0; j<elemx.size(); ++j, ++c){
			pcsolver->addCPBinaryRelVar(Literal(c), elemx[i], MNEQ, elemx[j]);
			if(i+j<n){
				vector<Literal> lits;
				lits.push_back(Literal(left));
				lits.push_back(Literal(c+i+1));
				pcsolver->addClause(lits);
			}
		}
	}*/

	return pcsolver;
}
