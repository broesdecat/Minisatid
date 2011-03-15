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

namespace MinisatID{

namespace Print{
	std::string getProgramVersion();
	std::string getProgramInfo();

	void printMainStart(int v);
	void printMainEnd(int v);

	void printInitDataStart(int v);
	void printInitDataEnd(int v, double parsetime, bool unsat);

	void printSimpStart(int v);
	void printSimpEnd(int v, double parsetime, bool unsat);

	void printSolveStart(int v);
	void printSolveEnd(int v, double parsetime);

	void printStartStatistics();

	void printUnsat(int v);

	template<class T, class T2>
	void printExceptionCaught(T2& stream, const T& e){
		stream<<">>> " <<e.what();
		stream<<">>> Program will abort.\n";
	}

	template<class T>
	std::string getParseError(const T& e, int linepos, int charpos, const char* yytext){
		std::stringstream ss;
		ss<<">> Parse error: Line " <<linepos <<", column " <<charpos <<", on \"" <<yytext <<"\": " << e.what();
		return ss.str();
	}

	template<class T>
	void printUnexpectedError(T& stream){
		stream <<">>> Unexpected error caught, program will abort.\n";
	}

	template<class T, class T2>
	void printPrimesFileNotReadable(T& stream, const T2& file){
		stream <<">> The file containing the list of primes could not be found in " <<file <<" .\n";
		stream <<">> Please place the file there, add a (different) --primesfiles commandline argument or recompile/reinstall.\n";
	}

	std::string getMinimalVarNumbering();

	template<class T>
	void printSatisfiable(T& stream, INPUTFORMAT inputformat, OUTPUTFORMAT outputformat, int verbosity = 1000){
		if(verbosity>=1){
			if(inputformat==FORMAT_OPB){
				stream<<"s SATISFIABLE\n";
			}else if(outputformat==TRANS_ASP){
				stream <<"ANSWER SET FOUND\n";
			}else{
				stream<<"SATISFIABLE\n";
			}
		}
	}

	template<class T>
	void printUnSatisfiable(T& stream, INPUTFORMAT inputformat, OUTPUTFORMAT outputformat, int verbosity = 1000){
		if(verbosity>=1){
			if(inputformat==FORMAT_OPB){
				stream<<"s UNSATISFIABLE\n";
			}else if(outputformat==TRANS_ASP){
				stream <<"INCONSISTENT\n";
			}else{
				stream<<"UNSATISFIABLE\n";
			}
		}
	}

	template<class T>
	void printOptimalModelFound(T& stream, INPUTFORMAT format, int verbosity = 1000){
		if(verbosity>=1){
			if(format==FORMAT_OPB){
				stream<<"s OPTIMUM FOUND\n";
			}else{
				stream<<"OPTIMUM FOUND\n";
			}
		}
	}

	template<class T>
	void printNoMoreModels(T& stream, int verbosity = 1000){
		if (verbosity >= 1) {
			stream <<"> No more models exist.\n";
		}
	}

	template<class T>
	void printNoModels(T& stream, int verbosity = 1000){
		if (verbosity >= 1) {
			stream <<"> No models exist.\n";
		}
	}

	template<class T>
	void printModuleNotPresent(T& stream, std::string name, int verbosity = 1000){
		if (verbosity > 0) {
			stream <<">    (there will be no propagations on " <<name <<" module)\n";
		}
	}

	template<class T>
	void printNbModels(T& stream, int found, int verbosity = 1000){
		if(verbosity>=1){
			stream <<"> " <<found <<" model" <<(found>1?"s":"") <<" found\n";
		}
	}

	template<class T>
	void printUnsatFoundDuringParsing(T& stream, int verbosity = 1000){
		stream << "> Unsat detected during parsing.\n";
	}

	template<class T>
	void printSetWatchRatio(T& stream, int setid, double ratio, int verbosity = 1000){
		if(verbosity>=4){
			stream <<"> Set " <<setid <<": watch ratio of " <<ratio <<"\n";
		}
	}

	template<class T>
	void printAddingClause(T& stream, const InnerDisjunction& disj, std::string modID, int verbosity = 1000){
		if (verbosity >= 2) {
			stream <<"Adding clause:";
			for (int i = 0; i < disj.literals.size(); i++) {
				stream <<" " <<disj.literals[i];
			}
			if(modID != ""){
				stream <<" to modal solver " <<modID <<" ";
			}
			stream <<"\n";
		}
	}
}

}

#endif /* PRINTMESSAGE_HPP_ */
