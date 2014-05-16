/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */

#include "Symmetry.hpp"

#include "satsolver/SATSolver.hpp"
#include "utils/Print.hpp"
#include "external/ConstraintVisitor.hpp"

using namespace std;
using namespace MinisatID;
using namespace Minisat;

SymmetryPropagator::SymmetryPropagator(PCSolver* solver, const Symmetry& sym)
		: 	Propagator(solver, "symmetry propagator"),
			symmetrical(sym.getSymmetrical()),
			inverse(sym.getInverse()),
			nextToPropagate(0) {
	getPCSolver().accept(this);
	getPCSolver().accept(this, EV_BACKTRACK);
	getPCSolver().accept(this, EV_PROPAGATE);
	for (auto litpair : symmetrical) {
		getPCSolver().accept(this, litpair.first, FAST);
		// NOTE: negation of litpair.first is always in the symmetrical-map, so no need to add it twice.
	}
}

void SymmetryPropagator::accept(ConstraintVisitor&) {
	throw notYetImplemented("Acceptance in Symmprop"); // TODO
}

/*
 * @return:
 * 	1: you can never propagate l without a backtrack
 * 	2: you can not propagate l now, but maybe after more assignments
 * 	3: you can propagate l now
 */
int SymmetryPropagator::canPropagate(Lit l) {
	if (getPCSolver().isDecided(l.getAtom()) || symmetrical.count(l) == 0 || getPCSolver().value(symmetrical.at(l)) == l_True) {
		return 1;
	}
	if (getPCSolver().getLevel(l.getAtom()) == 0) {
		return 3;
	}

	rClause cl = getPCSolver().getExplanation(l);
	int nbUndefs = 0;
	for (int i = 0; i < getPCSolver().getClauseSize(cl); ++i) {
		lbool val = getPCSolver().value(getSymmetrical(getPCSolver().getClauseLit(cl, i)));
		if (val == l_True) {
			return 1;
		} else if (val == l_Undef) {
			++nbUndefs;
			if (nbUndefs >= 2) {
				return 2;
			}
		}
	}

	return 3;
}

Lit SymmetryPropagator::getNextToPropagate() {
	for (unsigned int i = 0; i < potentialLits.size(); ++i) {
		int result = canPropagate(potentialLits.at(i));
		if (result == 3) {
			Lit propagatable = potentialLits.at(i);
			potentialLits[i] = potentialLits.back();
			potentialLits.pop_back(); // TODO: this line is missing from Minisat+Full Symmetry Propagation
			return propagatable;
		}
		if (result == 1) {
			potentialLits[i] = potentialLits.back();
			potentialLits.pop_back();
			--i;
		}
	}

	while ((unsigned int) nextToPropagate < getPCSolver().getTrail().size()) {
		Lit next = getPCSolver().getTrail().at(nextToPropagate);
		++nextToPropagate;
		int result = canPropagate(next);
		if (result == 3) {
			return next;
		} else if (result == 2) {
			potentialLits.push_back(next);
		}
	}

	return lit_Undef;
}

rClause SymmetryPropagator::notifypropagate() {
	Lit l = getNextToPropagate();
	if (l == lit_Undef) {
		return nullPtrClause;
	}
	std::vector<Lit> symClause;
	if (getPCSolver().getLevel(l.getAtom()) == 0) {
		// TODO: @Broes: is this the right trick to use for a propagation / conflict at level 0?
		symClause.push_back(symmetrical.at(l));
		symClause.push_back(not l);
	} else {
		getSymmetricalClause(getPCSolver().getExplanation(l), symClause);
	}
	auto c = getPCSolver().createClause(Disjunction(symClause), true);
	bool isConflict = true;
	for (auto ll : symClause) {
		MAssert(getPCSolver().value(ll)==l_Undef || getPCSolver().value(ll)==l_False);
		if (getPCSolver().value(ll) == l_Undef) {
			isConflict = false;
			break;
		}
	}
	if (isConflict) {
		if (verbosity() > 1) {
			cout << "Symmetry propagation detected conflict!" << endl;
			for(auto ll: symClause){
				cout << ll.x << ",";// << "-" << getPCSolver().value(ll) << "|";
			}
			cout << endl;
		}
		getPCSolver().addConflictClause(c);
		return c;
	} else {
		if (verbosity() > 1) {
			cout << "Symmetry propagation detected propagation!" << endl;
			for(auto ll: symClause){
				cout << ll.x << ",";// << "-" << getPCSolver().value(ll) << "|";
			}
			cout << endl;
		}
		getPCSolver().addLearnedClause(c);
		return nullPtrClause;
	}
}

// TODO: should anything be sorted? As in: lowest levels literals in front for conflict clauses, or undef literals in front for unit clauses?
// This was needed in Minisat, but does not seem needed in MinisatID
void SymmetryPropagator::getSymmetricalClause(rClause in_clause, vector<Lit>& out_clause) {
	out_clause.clear();
	int in_size = getPCSolver().getClauseSize(in_clause);
	out_clause.reserve(in_size);
	for (int i = 0; i < in_size; ++i) {
		Lit symLit = getSymmetrical(getPCSolver().getClauseLit(in_clause, i));
		out_clause.push_back(symLit);
	}
}

void SymmetryPropagator::notifyBacktrack(int, const Lit&) {
	// TODO: optimize
	nextToPropagate = 0;
	potentialLits.clear();
}

Lit SymmetryPropagator::getSymmetrical(Lit in){
	if(symmetrical.count(in)==0){
		return in;
	}else{
		return symmetrical.at(in);
	}
}

