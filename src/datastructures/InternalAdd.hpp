/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#pragma once

// NOTE: do NOT use for external applications, use Constraints.hpp instead!

#include "external/ExternalUtils.hpp"

namespace MinisatID{

template<typename VarList, typename ConstraintDB>
void addVars(const VarList& vars, TheoryID theoryid, ConstraintDB& engine) {
	for (auto i = vars.cbegin(); i < vars.cend(); ++i) {
		engine.createVar(*i, theoryid);
	}
}

template<typename Constraint, typename ConstraintDB>
void internalAdd(const Constraint& obj, TheoryID id, ConstraintDB& engine){
	addVars(obj.getAtoms(), id, engine);
	engine.getFactory(id).add(obj);
}

template<typename ConstraintDB>
void internalAdd(const SubTheory& obj, TheoryID id, ConstraintDB& engine){
	addVars(obj.getAtoms(), id, engine);
	std::vector<Atom> atoms = {obj.head};
	addVars(atoms, id, engine);
	engine.add(obj);
	addVars(obj.getAtoms(), obj.childid, engine);
}

}
