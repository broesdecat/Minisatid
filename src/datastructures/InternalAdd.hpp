/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef INTERNALADD_HPP_
#define INTERNALADD_HPP_

// NOTE: do NOT use for external applications, use Constraints.hpp instead!

#include "external/ExternalUtils.hpp"

namespace MinisatID{

template<typename VarList, typename ConstraintDB>
void addVars(const VarList& vars, ConstraintDB& engine) {
	for (auto i = vars.cbegin(); i < vars.cend(); ++i) {
		engine.createVar(*i);
	}
}

template<typename Constraint, typename ConstraintDB>
void add(const Constraint& obj, ConstraintDB& engine){
	addVars(obj.getAtoms(), engine);
	engine.getFactory().add(obj);
}
}

#endif /* INTERNALADD_HPP_ */
