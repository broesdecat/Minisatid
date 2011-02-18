//LICENSEPLACEHOLDER
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

std::string Print::getMinimalVarNumbering(){
	return "Variables can only be numbered starting from 1.\n";
}
