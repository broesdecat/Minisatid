/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */

#include"Datastructures.hpp"

namespace MinisatID {

EqType invertEqType(EqType type) {
	switch (type) {
	case EqType::EQ:
	case EqType::NEQ:
		return type;
	case EqType::L:
		return EqType::G;
	case EqType::G:
		return EqType::L;
	case EqType::GEQ:
		return EqType::LEQ;
	case EqType::LEQ:
		return EqType::GEQ;
	}
}

}
