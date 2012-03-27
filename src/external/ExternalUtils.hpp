/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef EXTERNALUTILS_HPP_
#define EXTERNALUTILS_HPP_

typedef unsigned int uint;

#include <sstream>

#ifndef NDEBUG
#define MAssert(condition) { if(!(condition)){ std::stringstream ss; ss << "ASSERT FAILED: " << #condition << " @ " << __FILE__ << " (" << __LINE__ << ")"; throw idpexception(ss.str());} }
#else
#define MAssert(x) do {} while(0)
#endif

#include "Idpexception.hpp"
#include "Weight.hpp"
#include "Datastructures.hpp"
#include "LazyClauseSupport.hpp"
#include "TerminationManagement.hpp"
#include "Options.hpp"

#endif /*EXTERNALUTILS_HPP_*/
