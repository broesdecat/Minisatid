/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef PARSEOPTIONS_HPP_
#define PARSEOPTIONS_HPP_

#include "external/Options.hpp"

namespace MinisatID{
	bool parseOptions(int argc, char** argv, SolverOption& modes);
}

#endif /* PARSEOPTIONS_HPP_ */
