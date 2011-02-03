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

#include "utils/PrintMessage.hpp"

#include "utils/Utils.hpp"
#include <iostream>

using namespace std;
using namespace MinisatID;
using namespace MinisatID::Print;

string Print::getProgramVersion(){
	return "2.4.0";
}

string Print::getProgramInfo(){
	string programInfo =
		"MinisatID is a model generator for the language ECNF, an extension of CNF with aggregates expressions"
		"(sum, cardinality, min, max, product) and inductive definitions.\n"
		"Several other well-known input formats are also supported:\n"
		"\t - ground LParse, used within the domain of answer-set programming.\n"
		"\t - QBF, used within the domain of quantified boolean formula reasoning (experimental support!).\n"
		"\t - OPB, used within the domain of pseudo-boolean constraint solving.\n\n"
		"MinisatID is part of the IDP system, a knowledge base system based on the FO(.) language. IDP supports, "
		"among others, state-of-the-art model expansion inference.\n\n"
		"MinisatID is the courtesy of the Knowledge Representation and Reasoning (KRR) group at the K.U. Leuven, "
		"Belgium and is maintained by Broes De Cat. More information on the systems and the research can be found "
		"on \"http://dtai.cs.kuleuven.be/krr\".\n";
	return programInfo;
}

void Print::printMainStart(int v) {
	if (v >= 1) {
		clog <<">>> [ Problem Stats ]\n";
		clog <<"> Parsing input.\n";
	}
}

void Print::printInitDataStart(int v) {
	if (v >= 1) {
		clog <<"> Datastructure initialization.\n";
	}
}

void Print::printInitDataEnd(int v, double parsetime, bool unsat) {
	if (v >= 1) {
		clog <<"> Datastructure initialization finished.\n";
		clog <<"> Total parsing time : " << parsetime <<" s.\n";
	}
	if (v >= 1 && unsat) {
		clog <<"> Unsatisfiable found by parsing.\n";
	}
}

void Print::printSimpStart(int v) {
	if (v >= 1) {
		clog <<">>> [ Simplifying ]\n";
	}
}
void Print::printSimpEnd(int v, bool unsat) {
	if (v >= 1 && unsat) {
		clog <<"> Unsatisfiable found by unit propagation.\n";
	}
}

void Print::printSolveStart(int v) {
	if (v >= 1) {
		clog <<">>> [ Solving ]\n";
	}
}
void Print::printSolveEnd(int v) {
}

void Print::printPrimesFileNotReadable(ostream& stream, const char* file){
	stream << "The file containing a list of primes could not be found or is not readable. Please put it in \""
			<<file <<"\" or recompile.\n";
}

std::string Print::getMinimalVarNumbering(){
	return "Variables can only be numbered starting from 1.\n";
}
