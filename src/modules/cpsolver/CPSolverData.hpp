/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#pragma once

#include <vector>

#include "modules/cpsolver/CPUtils.hpp"

namespace MinisatID {
class TermIntVar;
class ReifiedConstraint;
class GecodeConstraint;
class CPScript;

class CPSolverData {
private:
	std::vector<CPScript*> history;
	std::map<VarID,TermIntVar> terms;
	std::vector<GecodeConstraint*> nonreifconstraints;
	std::map<Atom,ReifiedConstraint*> reifconstraints;

public:
	CPSolverData();
	virtual ~CPSolverData();

	CPScript& getSpace() const {
		return *history.back();
	}
	CPScript& getPrevSpace() const {
		MAssert(history.size() > 1);
		return *history[history.size() - 2];
	}

	void replaceLastWith(CPScript* space);

	void addSpace();
	void removeSpace();

	const std::map<VarID,TermIntVar>& getTerms() const {
		return terms;
	}
	void addTerm(const TermIntVar& var);

	const std::vector<GecodeConstraint*>& getNonReifConstraints() const {
		return nonreifconstraints;
	}
	const std::map<Atom,ReifiedConstraint*>& getReifConstraints() const {
		return reifconstraints;
	}

	//owning pointers
	void addReifConstraint(ReifiedConstraint* c);
	void addNonReifConstraint(GecodeConstraint* c) {
		nonreifconstraints.push_back(c);
	}

	TermIntVar convertToVar(VarID term) const;
	std::vector<TermIntVar> convertToVars(const std::vector<VarID>& terms) const;
};
}
