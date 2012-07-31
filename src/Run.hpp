/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef RUN_HPP_
#define RUN_HPP_

#include <string>
#include "external/Options.hpp"

namespace MinisatID{
	class ExternalConstraintVisitor;

	int run(const std::string& inputfile, SolverOption modes);

	void parseAndInitializeTheory(const std::string& inputfile, ExternalConstraintVisitor* d);
}


#endif /* RUN_HPP_ */
