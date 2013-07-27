/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#include "theorysolvers/PCSolver.hpp"

#include <iostream>
#include "TheorySimplifier.hpp"
#include "PCSolver.hpp"

using namespace std;
using namespace MinisatID;

void TheorySimplifier::add(const CPBinaryRel& obj) {
	auto canon = canonify(obj);

	auto& engine = factory->getEngine();
	std::stringstream ss;
	if (canon.rel == EqType::EQ) {
		presentEQcomps[canon.varID][canon.bound] = canon.head;
		ss << engine.toString(obj.varID) << "=" << obj.bound;
	} else {
		presentLEQcomps[canon.varID][canon.bound] = canon.head;
		ss << engine.toString(obj.varID) << "=<" << obj.bound;
	}
	engine.setString(canon.head.getAtom(), ss.str());
	internalAdd(obj);
}
