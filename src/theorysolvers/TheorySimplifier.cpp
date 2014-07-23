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

#warning todo: simplify equivalences A <=> B

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

CPBinaryRel TheorySimplifier::canonify(const CPBinaryRel& incomp) const {
	auto temp = incomp;
	switch (incomp.rel) {
	case EqType::EQ:
		break;
	case EqType::NEQ:
		temp.head = ~temp.head;
		temp.rel = EqType::EQ;
		break;
	case EqType::LEQ:
		break;
	case EqType::GEQ:
		temp.head = ~temp.head;
		temp.bound -= 1;
		temp.rel = EqType::LEQ;
		break;
	case EqType::G:
		temp.head = ~temp.head;
		temp.rel = EqType::LEQ;
		break;
	case EqType::L:
		temp.bound -= 1;
		temp.rel = EqType::LEQ;
		break;
	}
	return temp;
}

// Return literal 0 if it does not exist yet.
Lit TheorySimplifier::exists(const CPBinaryRel& comp) const {
	auto canoncomp = canonify(comp);
	if (canoncomp.rel == EqType::EQ) {
		auto it = presentEQcomps.find(canoncomp.varID);
		if (it == presentEQcomps.cend()) {
			return comp.head;
		}
		auto litit = it->second.find(canoncomp.bound);
		if (litit == it->second.cend()) {
			return comp.head;
		} else {
			return litit->second;
		}
	} else { // Leq
		auto it = presentLEQcomps.find(canoncomp.varID);
		if (it == presentLEQcomps.cend()) {
			return comp.head;
		}
		auto litit = it->second.find(canoncomp.bound);
		if (litit == it->second.cend()) {
			return comp.head;
		} else {
			return litit->second;
		}
	}
}
