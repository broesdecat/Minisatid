/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#include "utils/PrintMessage.hpp"

#include "utils/Utils.hpp"
#include <iostream>

using namespace std;
using namespace MinisatID;
using namespace MinisatID::Print;

string Print::getProgramVersion(){
	return VERSION;
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

void Print::printStatistics(double parsetime, double simpltime, double solvetime){
	clog <<">>> [Statistics]\n";
	if(parsetime>=0){
		clog <<">>> Parsing phase took " << parsetime <<" sec.\n";
	}
	if(simpltime>=0){
		clog <<">>> Simplication phase took " << simpltime <<" sec.\n";
	}
	if(solvetime>=0){
		clog <<">>> (last) solving phase took " << solvetime <<" sec.\n";
	}
}

void Print::printInitDataEnd(int v, bool unsat) {
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
	if (v >= 1) {
		if(unsat){
			clog <<"> Unsatisfiable found by unit propagation.\n";
		}
	}
}

void Print::printSolveStart(int v) {
	if (v >= 1) {
		clog <<">>> [ Solving ]\n";
	}
}

std::string Print::getMinimalVarNumbering(){
	return ">> Variables can only be numbered starting from 1.\n";
}
