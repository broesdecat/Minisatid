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
	void printStatistics(T obj, int v = 1000){
		if(v>=1){
			obj->printStatistics();
		}
	}

	template<class T>
	void printUnexpectedError(T& stream){
		stream <<">>> Unexpected error caught, program will abort.\n";
	}

	void printPrimesFileNotReadable(std::ostream& stream, const char* file);

	std::string getMinimalVarNumbering();

	template<class T>
	void printSatisfiable(T& stream, int verbosity = 1000){
		if(verbosity>=1){
			stream <<"SATISFIABLE\n";
		}
	}

	template<class T>
	void printUnSatisfiable(T& stream, int verbosity = 1000){
		if(verbosity>=1){
			stream <<"UNSATISFIABLE\n";
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

	template<class T>
	int getPrintableVar(T v){
		return v+1;
	}

	template<class T>
	void print(const T& lit, const lbool val){
		std::clog <<(sign(lit)?"-":"") <<getPrintableVar(var(lit)) <<":" <<(val==l_True?'1':(val==l_False?'0':'X'));
	}

	template<class T>
	void print(const T& lit){
		std::clog <<(sign(lit)?"-":"") <<getPrintableVar(var(lit));
	}

	template<class T>
	void printClause(const T& c){
		for(int i=0; i<c.size(); i++){
			printLit(c[i]); std::clog <<" ";
		}
	}
}

}

#endif /* PRINTMESSAGE_HPP_ */
