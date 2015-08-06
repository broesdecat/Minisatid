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

string MinisatID::getProgramVersion(){
	return std::string("")+VERSION + " -(" + MINISATIDGITHASH + ")";
}

string MinisatID::getProgramInfo(){
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

std::string MinisatID::getNoCPSupportString(){
	return "Constraint Programming support not compiled in, please recompile with --enable-cp=yes.\n";
}

std::string MinisatID::getMultipleDefAggHeadsException(){
	return "Multiple heads occurred with the same head and at least one of them was defined.\n";
}

void MinisatID::printMainStart(int v) {
	if (v >= 1) {
		clog <<">>> [ Problem Stats ]\n";
		clog <<"> Parsing input.\n";
	}
}

void MinisatID::printInitDataStart(int v) {
	if (v >= 1) {
		clog <<"> Datastructure initialization.\n";
	}
}

std::string MinisatID::getStatisticsMessage(double parsetime, double simpltime, double solvetime){
	stringstream ss;
	ss <<">>> [Statistics]\n";
	if(parsetime>=0){
		ss <<">>> Parsing phase took " << parsetime <<" sec.\n";
	}
	if(simpltime>=0){
		ss <<">>> Simplication phase took " << simpltime <<" sec.\n";
	}
	if(solvetime>=0){
		ss <<">>> (last) solving phase took " << solvetime <<" sec.\n";
	}
	return ss.str();
}

void MinisatID::printInitDataEnd(int v, bool unsat) {
	if (v >= 1 && unsat) {
		clog <<"> Unsatisfiable found by parsing.\n";
	}
}


void MinisatID::printSolveStart(int v) {
	if (v >= 1) {
		clog <<">>> [ Solving ]\n";
	}
}

bool headerprinted = false;
bool MinisatID::headerAlreadyPrinted(){
	return headerprinted;
}
void MinisatID::notifyHeaderPrinted(){
	headerprinted = true;
}
