#include "utils/PrintMessage.hpp"
#include "utils/Utils.hpp"

using namespace MinisatID;
using namespace MinisatID::Print;

void Print::printDataInitStart(int v) {
	if(v>=2){
		report("| Datastructure initialization                                                |\n");
	}
}

void Print::printDataInitEnd(int v) {

}

void Print::printMainStart(int v) {
	if (v >= 1) {
		report("============================[ Problem Statistics ]=============================\n");
		report("| Parsing input                                                               |\n");
	}
}

void Print::printMainEnd(int v) {

}

void Print::printExceptionCaught(const idpexception& e, int v){
	report("%s\n", e.what());
	report("Program will abort.\n");
}

void Print::printUnexpectedError(int v){
	report("Unexpected error caught, program will abort.\n");
}
