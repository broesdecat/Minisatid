/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef PRINTMESSAGE_HPP_
#define PRINTMESSAGE_HPP_

#include <exception>
#include <sstream>
#include <string>

#include "utils/Utils.hpp"

namespace MinisatID {

std::string getProgramVersion();
std::string getProgramInfo();

void printMainStart(int v);
void printMainEnd(int v);

void printInitDataStart(int v);
void printInitDataEnd(int v, bool unsat);

void printSimpStart(int v);
void printSimpEnd(int v, bool unsat);

void printSolveStart(int v);

std::string getStatisticsMessage(double parsetime, double simpltime,
		double solvetime);

void printUnsat(int v);

template<class T, class T2>
void printExceptionCaught(T2& stream, const T& e) {
	stream << ">>> " << e.what();
	stream << ">>> Program will abort.\n";
}

template<class T>
std::string getParseError(const T& e, int linepos, const char* yytext) {
	std::stringstream ss;
	ss << ">> Parse error at line " << linepos << " on \"" << yytext << "\": "
			<< e.what();
	return ss.str();
}

template<class T>
void printUnknown(T& stream, OutputFormat outputformat) {
	if (outputformat == OutputFormat::FZ) {
		stream << "=====UNKNOWN=====\n";
	} else {
		stream << "UNKNOWN\n";
	}
}

template<class T>
void printUnexpectedError(T& stream) {
	stream << ">>> Unexpected error caught, program will abort.\n";
}

template<class T, class T2>
void printPrimesFileNotReadable(T& stream, const T2& file) {
	stream << ">> The file containing the list of primes could not be found in "
			<< file << " .\n";
	stream
			<< ">> Please place the file there, add a (different) --primesfiles commandline argument or recompile/reinstall.\n";
}

template<class T>
void printSatisfiable(T& stream, OutputFormat outputformat,
		int verbosity = 1000) {
	if (verbosity >= 1) {
		if (outputformat == OutputFormat::OPB) {
			stream << "s SATISFIABLE\n";
		} else if (outputformat == OutputFormat::ASP) {
			stream << "ANSWER\n";
		} else if (outputformat == OutputFormat::FZ) {
			// No output
		} else {
			stream << "SATISFIABLE\n";
		}
	}
}

template<class T>
void printUnSatisfiable(T& stream, OutputFormat outputformat, int verbosity =
		1000) {
	if (verbosity >= 1) {
		if (outputformat == OutputFormat::OPB) {
			stream << "s UNSATISFIABLE\n";
		} else if (outputformat == OutputFormat::ASP) {
			stream << "INCONSISTENT\n";
		} else if (outputformat == OutputFormat::FZ) {
			stream << "=====UNSATISFIABLE=====\n";
		} else {
			stream << "UNSATISFIABLE\n";
		}
	}
}

template<class T>
void printOptimalModelFound(T& stream, OutputFormat outputformat,
		int verbosity = 1000) {
	if (verbosity >= 1) {
		if (outputformat == OutputFormat::OPB) {
			stream << "s OPTIMUM FOUND\n";
		} else if (outputformat == OutputFormat::FZ) {
			// TODO flatzinc optimisation output will probably be revised next year
			stream <<"==========\n";
		} else if (outputformat == OutputFormat::ASP) {
			stream << "OPTIMUM\n";
		} else {
			stream << "OPTIMUM FOUND\n";
		}
	}
}

template<class T>
void printNoMoreModels(T& stream, OutputFormat outputformat) {
	if (outputformat == OutputFormat::FZ) {
		stream << "==========\n";
	}
}

template<class T>
void printNoMoreModels(T& stream, int verbosity = 1000) {
	if (verbosity >= 1) {
		stream << "> No more models exist.\n";
	}
}

template<class T>
void printNoModels(T& stream, int verbosity = 1000) {
	if (verbosity >= 1) {
		stream << "> No models exist.\n";
	}
}

bool headerAlreadyPrinted();
void notifyHeaderPrinted();
template<class T>
void printSearchStart(T& stream, int verbosity = 1000) {
	if (verbosity >= 1) {
		stream << ">>> Search start\n";
		if (!headerAlreadyPrinted()) {
			stream
					<< "> Conflicts |          ORIGINAL         |          LEARNT          | Progress\n";
			stream
					<< ">           |    Vars  Clauses Literals |    Limit  Clauses Lit/Cl |         \n";
			notifyHeaderPrinted();
		}
	}
}

template<class T>
void printSearchEnd(T& stream, int verbosity = 1000) {
	if (verbosity >= 1) {
		stream << ">>> Search done\n";
	}
}

template<class T>
void printSearchAborted(T& stream, int verbosity = 1000) {
	if (verbosity >= 1) {
		stream << ">>> Search aborted\n";
	}
}

template<class T>
void printModuleNotPresent(T& stream, std::string name, int verbosity = 1000) {
	if (verbosity > 0) {
		stream << ">    (there will be no propagations on " << name
				<< " module)\n";
	}
}

template<class T>
void printNbModels(T& stream, int found, int verbosity = 1000) {
	if (verbosity >= 1) {
		stream << "> " << found << " model" << (found > 1 ? "s" : "")
				<< " found\n";
	}
}

template<class T>
void printUnsatFoundDuringParsing(T& stream, int verbosity = 1000) {
	if (verbosity >= 1) {
		stream << "> Unsat detected during parsing.\n";
	}
}

template<class T>
void printSetWatchRatio(T& stream, int setid, double ratio,
		int verbosity = 1000) {
	if (verbosity >= 4) {
		stream << "> Set " << setid << ": watch ratio of " << ratio << "\n";
	}
}

template<class T>
void printNoPropagationsOn(T& stream, const std::string& name, int verbosity =
		1000) {
	if (verbosity > 0) {
		stream << ">    (there will be no propagations on " << name
				<< " module)\n";
	}
}

std::string getNoCPSupportString();
std::string getMultipleDefAggHeadsException();
}

#endif /* PRINTMESSAGE_HPP_ */
