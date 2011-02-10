//------------------------------------------------------------------------------
// Copyright (c) 2009, 2010, 2011, Broes De Cat, K.U. Leuven, Belgium
//
// This file is part of MinisatID.
//
// MinisatID is free software: you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// MinisatID is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with MinisatID. If not, see <http://www.gnu.org/licenses/>.
//------------------------------------------------------------------------------

#ifndef PRINTMESSAGE_HPP_
#define PRINTMESSAGE_HPP_

#include <exception>
#include <iostream>
#include <sstream>

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
	void printSimpEnd(int v, bool unsat);

	void printSolveStart(int v);
	void printSolveEnd(int v);

	void printUnsat(int v);

	template<class T, class T2>
	void printExceptionCaught(T2& stream, const T& e){
		stream<<">>> " <<e.what();
		stream<<">>> Program will abort.\n";
	}

	template<class T>
	std::string getParseError(const T& e, int linepos, int charpos, const char* yytext){
		std::stringstream ss;
		ss<<"Parse error: Line " <<linepos <<", column " <<charpos <<", on \"" <<yytext <<"\": " << e.what();
		return ss.str();
	}

	template<class T>
	void printUnexpectedError(T& stream){
		stream <<">>> Unexpected error caught, program will abort.\n";
	}

	template<class T, class T2>
	void printPrimesFileNotReadable(T& stream, const T2& file){
		stream <<"The file containing the list of primes could not be found in " <<file <<" .\n";
		stream <<"Please place the file there, add a (different) --primesfiles commandline argument or recompile/reinstall.\n";
	}

	std::string getMinimalVarNumbering();

	template<class T>
	void printSatisfiable(T& stream, ASPCOMP3TYPE type, int verbosity = 1000){
		if(verbosity>=1){
			if(type==ASPCOMP3_NOCOMP){
				stream <<"SATISFIABLE\n";
			}else if(type==ASPCOMP3_SEARCH){
				stream <<"ANSWER SET FOUND\n";
			}
		}
	}

	template<class T>
	void printUnSatisfiable(T& stream, ASPCOMP3TYPE type, int verbosity = 1000){
		if(verbosity>=1){
			if(type==ASPCOMP3_QUERY){
				stream <<"INCONSISTENT\n";
			}else if(type==ASPCOMP3_SEARCH){
				stream <<"NO ANSWER SET FOUND\n";
			}else{
				stream <<"UNSATISFIABLE\n";
			}
		}
	}

	template<class T>
	void printOptimalModelFound(T& stream, ASPCOMP3TYPE type, int verbosity = 1000){
		if(verbosity>=1){
			stream<<"OPTIMUM FOUND\n";
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
		stream << "Unsat detected during parsing.\n";
	}
}

}

#endif /* PRINTMESSAGE_HPP_ */
