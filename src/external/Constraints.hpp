/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef CONSTRAINTS_HPP_
#define CONSTRAINTS_HPP_

// IMPORTANT NOTE: Uses remapping, so never use for internal constraint creation!!!

#include "Space.hpp"

namespace MinisatID {

Var checkAtom(const Atom& atom, Remapper& remapper);
Lit checkLit(const Literal& lit, Remapper& remapper);
std::vector<Lit> checkLits(const std::vector<Literal>& lits, Remapper& remapper);
std::vector<std::vector<Lit> > checkLits(const std::vector<std::vector<Literal> >& lits, Remapper& remapper);
std::map<Lit, Lit> checkLits(const std::map<Literal, Literal>& lits, Remapper& remapper);
std::vector<Var> checkAtoms(const std::vector<Atom>& atoms, Remapper& remapper);
std::map<Var, Var> checkAtoms(const std::map<Atom, Atom>& atoms, Remapper& remapper);

template<typename Constraint, typename Engine>
class ExtAdd{
public:
	void extAdd(ConstraintAdditionInterface<Engine>& space, const Constraint& obj);
};

template<typename Constraint, typename Engine>
void extAdd(ConstraintAdditionInterface<Engine>& space, const Constraint& obj){
	ExtAdd<Constraint, Engine> f;
	f.extAdd(space, obj);
}
}

#endif /* CONSTRAINTS_HPP_ */
