/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#include <sstream>
#include <iostream>
#include <string>

#if defined(__linux__)
#include <fpu_control.h>
#endif

#include "Run.hpp"
#include "parser/CommandLineOptions.hpp"

using namespace std;
using namespace MinisatID;

int main(int argc, char** argv) {
	//Setting system precision and signal handlers
#if defined(__linux__)
	fpu_control_t oldcw, newcw;
	_FPU_GETCW(oldcw);
	newcw = (oldcw & ~_FPU_EXTENDED) | _FPU_DOUBLE;
	_FPU_SETCW(newcw);
	// double precision for repeatability
#endif

	//parse command-line options
	SolverOption modes;
	string inputfile = "";
	auto successfullparsing = parseOptions(argc, argv, modes, inputfile);
	if (not successfullparsing) {
		clog << ">>> Error during parsing of command-line options, aborting...";
		return 0;
	}

	return run(inputfile, modes);
}


