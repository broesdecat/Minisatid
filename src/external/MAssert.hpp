/************************************
	MAssert.hpp
	this file belongs to GidL 2.0
	(c) K.U.Leuven
************************************/

#pragma once

#include <sstream>
#include "Idpexception.hpp"

#ifndef NDEBUG
#define MAssert(condition) { if(!(condition)){ std::stringstream ss; ss << "ASSERT FAILED: " << #condition << " @ " << __FILE__ << " (" << __LINE__ << ")"; throw MinisatID::idpexception(ss.str());} }
#else
#define MAssert(x) do { (void)sizeof(x); } while(0)
#endif
