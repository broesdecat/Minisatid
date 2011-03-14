/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#include "utils/ECNFPrinter.hpp"
#include "utils/Print.hpp"

using namespace std;
using namespace MinisatID;
using namespace MinisatID::Print;

ECNFPrinter::ECNFPrinter() {}

ECNFPrinter::~ECNFPrinter() {}

void ECNFPrinter::startPrinting(){
	ss <<"graph ecnftheory {\n";
}

void ECNFPrinter::addClause(const vec<Lit>& lits){
	for(int i=0; i<lits.size(); i++){
		if(i>0){
			ss <<" -- ";
		}
		ss <<getPrintableVar(var(lits[i]));
	}
	if(lits.size()>1){
		ss <<" -- " <<getPrintableVar(var(lits[0])) <<" ";
	}
	ss <<"[color=blue];\n";
}

void ECNFPrinter::addSet(const vector<Lit>& lits){
	for(int i=0; i<lits.size(); i++){
		if(i>0){
			ss <<" -- ";
		}
		ss <<getPrintableVar(var(lits[i]));
	}
	if(lits.size()>1){
		ss <<" -- " <<getPrintableVar(var(lits[0])) <<" ";
	}
	ss <<"[color=green];\n";
}

void ECNFPrinter::endPrinting(ostream& stream){
	ss <<"}\n";
	stream <<ss;
}
