/*
 * Copyright 2007-2014 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Marien, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#include "external/ConstraintVisitor.hpp"
#include "utils/Print.hpp"

using namespace std;
using namespace MinisatID;

template<typename S>
void MinisatID::printList(const litlist& list, const std::string& concat, S& stream, LiteralPrinter* solver) {
	bool begin = true;
	for (auto i = list.cbegin(); i < list.cend(); ++i) {
		if (not begin) {
			stream << concat;
		}
		begin = false;
		stream << toString(*i, solver);
	}
}

template void MinisatID::printList(const litlist&, const std::string&, std::ostream&, LiteralPrinter*);
