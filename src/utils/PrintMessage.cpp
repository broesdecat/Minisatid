#include "utils/PrintMessage.hpp"
#include "utils/Utils.hpp"

using namespace MinisatID;
using namespace MinisatID::Print;

void Print::printMainStart(int v) {
	if (v >= 1) {
		report(">>> [ Problem Stats ]\n");
		report("> Parsing input.\n");
	}
}

void Print::printInitDataStart(int v) {
	if (v >= 1) {
		report("> Datastructure initialization.\n");
	}
}

void Print::printInitDataEnd(int v, double parsetime, bool unsat) {
	if (v >= 1) {
		report("> Datastructure initialization finished.\n");
		report("> Total parsing time : %7.2f s.\n", parsetime);
	}
	if (v >= 1 && unsat) {
		report("> Unsatisfiable found by parsing.\n");
	}
}

void Print::printSimpStart(int v) {
	if (v >= 1) {
		report(">>> [ Simplifying ]\n");
	}
}
void Print::printSimpEnd(int v, bool unsat) {
	if (v >= 1 && unsat) {
		report("> Unsatisfiable found by unit propagation.\n");
	}
}

void Print::printSolveStart(int v) {
	if (v >= 1) {
		report(">>> [ Solving ]\n");
	}
}
void Print::printSolveEnd(int v) {
}

void Print::printUnsat(int v){
	if(v >= 1){
		report("> UNSATISFIABLE\n");
	}
}

void Print::printExceptionCaught(const idpexception& e, int v) {
	report(">>> %s", e.what());
	report(">>> Program will abort.\n");
}

void Print::printUnexpectedError(int v) {
	report(">>> Unexpected error caught, program will abort.\n");
}
