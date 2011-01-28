#include "utils/PrintMessage.hpp"
#include "utils/Utils.hpp"
#include <iostream>

using namespace std;
using namespace MinisatID;
using namespace MinisatID::Print;

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

void Print::printUnsat(int v){
	if(v >= 1){
		clog <<"> UNSATISFIABLE\n";
	}
}

void Print::printExceptionCaught(const exception& e, int v) {
	cerr<<">>> " <<e.what() <<"\n";
	cerr <<">>> Program will abort.\n";
}

void Print::printUnexpectedError(int v) {
	cerr <<">>> Unexpected error caught, program will abort.\n";
}
