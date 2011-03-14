/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef ECNFPRINTER_HPP_
#define ECNFPRINTER_HPP_

#include <vector>
#include <sstream>
#include <iostream>
#include "utils/Utils.hpp"

namespace MinisatID{

class ECNFPrinter {
private:
	std::stringstream ss;

public:
	ECNFPrinter();
	virtual ~ECNFPrinter();

	void 	startPrinting();
	void 	endPrinting(std::ostream& stream);
	void 	addClause	(const vec<Lit>& lits);
	void 	addSet		(const std::vector<Lit>& lits);
};

}

#endif /* ECNFPRINTER_HPP_ */
