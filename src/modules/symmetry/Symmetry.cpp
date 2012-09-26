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

SymmetryData::SymmetryData(const Symmetry& symmetry) :
		symm(symmetry) {
	for (auto cycle = symmetry.symmetry.cbegin(); cycle != symmetry.symmetry.cend(); ++cycle) {
		MAssert((*cycle).size()>1);
		Lit previousLit = *cycle->cbegin();
		Lit firstLit= *cycle->cbegin();
		bool first = true;
		for (auto currentLit = cycle->cbegin(); currentLit != cycle->cend(); ++currentLit) {
			if (first) {
				firstLit = *currentLit;
				previousLit = firstLit;
				first = false;
			} else {
				sym[previousLit] = *currentLit;
				inverse[*currentLit] = previousLit;
				previousLit = *currentLit;
			}
		}
		sym[previousLit] = firstLit;
		inverse[firstLit] = previousLit;
	}
}

void SymmetryPropagator::accept(ConstraintVisitor& visitor) {
	visitor.add(symmetry.getSymmetry());
}

SymmetryPropagator::SymmetryPropagator(PCSolver* solver, const Symmetry& sym) :
		Propagator(DEFAULTCONSTRID, solver, "symmetry propagator"), symmetry(sym) {
	amountNeededForActive = 0;
	reasonOfPermInactive = lit_Undef;
	nextToPropagate = 0;

	for (auto i = symmetry.getSymmetryMap().cbegin(); i != symmetry.getSymmetryMap().cend(); ++i) {
		getPCSolver().accept(this, i->first, PRIORITY::FAST);

		// Var-order optimization
		if (i->first == (not i->second)) { // phase-changing optimization
			getPCSolver().varReduceActivity(var(i->first));
		}
	}

	getPCSolver().accept(this);
	getPCSolver().accept(this, EV_BACKTRACK);
	getPCSolver().accept(this, EV_DECISIONLEVEL);
}

#define getLit(clause, nb) (getPCSolver().getClauseLit(clause, nb))
#define lowerLevel(x, y) (getPCSolver().getLevel(var(x))<getPCSolver().getLevel(var(y)))

rClause SymmetryPropagator::notifypropagate() {
	while (hasNextProp()) {
		auto p = getNextProp();
		if (getSymmetrical(p) != p) {
			notifyEnqueued(p);
		}
	}
	auto confl = nullPtrClause;
	// weakly active symmetry propagation: the condition qhead==trail.size() makes sure symmetry propagation is executed after unit propagation
	Lit orig = lit_Undef;
	if (isActive()) {
		orig = getNextToPropagate();
		if (orig != lit_Undef) {
			confl = propagateSymmetrical(orig);
		}
	}
	return confl;
}

void SymmetryPropagator::notifyEnqueued(const Lit& l) {
	// Start with latest not yet propagated literals
	MAssert(getSymmetrical(l) != l);
	MAssert(value(l) == l_True);
	notifiedLits.push_back(l);

#ifdef DEBUG
	set<Atom> unique;
	for(auto i=notifiedLits.cbegin(); i<notifiedLits.cend(); ++i){
		auto it = unique.find(var(*i));
		MAssert(it==unique.cend());
		unique.insert(var(*i));
	}
#endif

	if (isPermanentlyInactive()) {
		return;
	}
	auto inverse = getInverse(l);
	auto symmetrical = getSymmetrical(l);

	if (getPCSolver().isDecided(var(inverse))) {
		if (value(inverse) == l_True) { //invar: value(l)==l_True
			--amountNeededForActive;
		} else {
			MAssert(getPCSolver().value(inverse) == l_False);
			reasonOfPermInactive = l;
		}
	}
	if (getPCSolver().isDecided(var(l))) {
		if (value(symmetrical) == l_Undef) {
			++amountNeededForActive;
		} else if (value(symmetrical) == l_False) {
			reasonOfPermInactive = l;
		}
		// else value(symmetrical) is true
	}
}

Lit SymmetryPropagator::getNextToPropagate() {
	if (not isActive()) {
		return lit_Undef;
	}

#ifdef DEBUG
	set<Atom> unique;
	for(auto i=notifiedLits.cbegin(); i<notifiedLits.cend(); ++i){
		auto it = unique.find(var(*i));
		MAssert(it==unique.cend());
		unique.insert(var(*i));
	}
#endif

#ifdef DEBUG
	for(auto j=notifiedLits.cbegin(); j<notifiedLits.cend(); ++j) {
		MAssert(value(*j)!=l_Undef);
	}
#endif

	while (nextToPropagate < notifiedLits.size()
			&& (getPCSolver().isDecided(var(notifiedLits[nextToPropagate])) || value(getSymmetrical(notifiedLits[nextToPropagate])) == l_True)) {
		++nextToPropagate;
	}
	MAssert(isActive());
	if (nextToPropagate == notifiedLits.size()) {
		return lit_Undef;
	} else {
		return notifiedLits[nextToPropagate];
	}
}

// Store activity and number of needed literals
void SymmetryPropagator::notifyNewDecisionLevel() {
	activityTrail.push_back(reasonOfPermInactive);
	amountNeededTrail.push_back(amountNeededForActive);
	notifiedLitTrail.push_back(notifiedLits);
	notifiedLits.clear();
}

// Reset activity and number of needed literals
void SymmetryPropagator::notifyBacktrack(int untillevel, const Lit& l) {
	nextToPropagate = 0;
	reasonOfPermInactive = activityTrail[untillevel];
	activityTrail.resize(untillevel + 1);
	amountNeededForActive = amountNeededTrail[untillevel];
	amountNeededTrail.resize(untillevel + 1);
	notifiedLits = notifiedLitTrail[untillevel];
	notifiedLitTrail.resize(untillevel + 1);
#ifdef DEBUG
	for(auto i=notifiedLitTrail.cbegin(); i<notifiedLitTrail.cend(); ++i) {
		for(auto j=(*i).cbegin(); j<(*i).cend(); ++j) {
			MAssert(value(*j)!=l_Undef);
		}
	}
	for(auto j=notifiedLits.cbegin(); j<notifiedLits.cend(); ++j) {
		MAssert(value(*j)!=l_Undef);
	}
#endif
	Propagator::notifyBacktrack(untillevel, l);
}

bool SymmetryPropagator::isActive() {
	return amountNeededForActive == 0 && not isPermanentlyInactive(); // Laatste test is nodig voor phase change symmetries
}

bool SymmetryPropagator::isPermanentlyInactive() {
	return reasonOfPermInactive != lit_Undef;
}

rClause SymmetryPropagator::propagateSymmetrical(const Lit& l) {
	MAssert(isActive());
	MAssert(value(getSymmetrical(l))!=l_True);

	Disjunction implic(DEFAULTCONSTRID, {});
	if (getPCSolver().getLevel(var(l)) == 0) {
		implic.literals.push_back(getSymmetrical(l));
		implic.literals.push_back(~l);
	} else {
		auto reason = getPCSolver().getExplanation(l);
		MAssert(reason!=CRef_Undef);
		getSortedSymmetricalClause(reason, implic.literals);
	}
	auto symlit = implic.literals[0];
	MAssert(value(symlit)!=l_True);

	auto clause = nullPtrClause;
	if (value(symlit) == l_Undef) {
		add(implic);
		if (getPCSolver().isUnsat()) { // FIXME add methods should return the conflict clause if applicable
			clause = getPCSolver().createClause(implic, true);
			getPCSolver().addConflictClause(clause);
			return clause;
		}
	} else {
		clause = getPCSolver().createClause(implic, true);
		getPCSolver().addConflictClause(clause);
	}
	return clause;
}

//	@pre:	in_clause is clause without true literals
//	@post: 	out_clause is one of three options, depending on the number of unknown literals:
//			all false literals with first most recent and second second recent
//			first literal unknown, rest false and second most recent
//			first two literals unknown
void SymmetryPropagator::getSortedSymmetricalClause(const rClause& in_clause, std::vector<Lit>& out_clause) {
	auto insize = getPCSolver().getClauseSize(in_clause);
	MAssert(insize >= 2);
	int first = 0;
	int second = 1;
	out_clause.clear();

	out_clause.push_back(getSymmetrical(getLit(in_clause, 0)));
	for (int i = 1; i < insize; ++i) {
		out_clause.push_back(getSymmetrical(getLit(in_clause, i)));
		MAssert(value(out_clause[i]) != l_True);
		if (value(out_clause[first]) != l_Undef && (value(out_clause[i]) == l_Undef || lowerLevel(out_clause[first], out_clause[i]))) {
			second = first;
			first = i;
		} else if (value(out_clause[second]) != l_Undef && (value(out_clause[i]) == l_Undef || lowerLevel(out_clause[second], out_clause[i]))) {
			second = i;
		}
	}

	// note: swapping the final literals to their place is pretty tricky. Imagine for instance the case where first==0 or second==1 ;)
	if (first != 0) {
		Lit temp = out_clause[0];
		out_clause[0] = out_clause[first];
		out_clause[first] = temp;
	}
	MAssert(second != first);
	if (second == 0) {
		second = first;
	}
	if (second != 1) {
		Lit temp = out_clause[1];
		out_clause[1] = out_clause[second];
		out_clause[second] = temp;
	}
}
