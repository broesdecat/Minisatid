//--------------------------------------------------------------------------------------------------
//    Copyright (c) 2009-2010, Broes De Cat, K.U.Leuven, Belgium
//    
//    Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
//    associated documentation files (the "Software"), to deal in the Software without restriction,
//    including without limitation the rights to use, copy, modify, merge, publish, distribute,
//    sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
//    furnished to do so, subject to the following conditions:
//    
//    The above copyright notice and this permission notice shall be included in all copies or
//    substantial portions of the Software.
//    
//    THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
//    NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
//    NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
//    DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
//    OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
//--------------------------------------------------------------------------------------------------

/************************************************************************************
 Copyright (c) 2006-2009, Maarten Mariën

 Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
 associated documentation files (the "Software"), to deal in the Software without restriction,
 including without limitation the rights to use, copy, modify, merge, publish, distribute,
 sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
 furnished to do so, subject to the following conditions:

 The above copyright notice and this permission notice shall be included in all copies or
 substantial portions of the Software.

 THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
 NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
 DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
 OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 **************************************************************************************************/
/****************************************************************************************[Main.c]
 MiniSat -- Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson

 Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
 associated documentation files (the "Software"), to deal in the Software without restriction,
 including without limitation the rights to use, copy, modify, merge, publish, distribute,
 sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
 furnished to do so, subject to the following conditions:

 The above copyright notice and this permission notice shall be included in all copies or
 substantial portions of the Software.

 THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
 NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
 DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
 OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 **************************************************************************************************/

#include <ctime>
#include <cstring>
#include <stdint.h>
#include <cerrno>
#include <iostream>
#include <fstream>
#include <signal.h>
#include <tr1/memory>
#include <sstream>

#include "solvers/parser/ParseOptions.hpp"

#include <setjmp.h>

#include "solvers/external/ExternalInterface.hpp"
#include "solvers/Unittests.hpp"
#include "solvers/parser/Lparseread.hpp"
#include "solvers/parser/PBread.hpp"

//#include "solvers/utils/PrintMessage.hpp"

#if defined(__linux__)
#include <fpu_control.h>
#endif

using namespace std;
using namespace std::tr1;
using namespace MinisatID;
//using namespace MinisatID::Print;

namespace MinisatID {
	class WrappedLogicSolver;
	typedef shared_ptr<WrappedLogicSolver> pData;
}

extern char * yytext;
extern int lineNo;
extern int charPos;
extern pData getData();

//extern FILE*	ecnfin;
//extern int	ecnfparse	();
extern FILE* yyin;
extern int yyparse();
extern void yydestroy();
extern void yyinit();
extern bool unsatfound;

const char* hasPrefix(const char* str, const char* prefix);
pData parse();

void printStats();

jmp_buf main_loop;
static void noMoreMem();
volatile sig_atomic_t mem;
static void SIGINT_handler(int signum);

int doModelGeneration(pData& d, double cpu_time);

extern SolverOption modes;

///////
// MAIN METHOD
///////

int main(int argc, char** argv) {
	//Setting system precision and signal handlers
#if defined(__linux__)
	fpu_control_t oldcw, newcw;
	_FPU_GETCW(oldcw);
	newcw = (oldcw & ~_FPU_EXTENDED) | _FPU_DOUBLE;
	_FPU_SETCW(newcw); // double precision for repeatability
#endif
	signal(SIGINT, SIGINT_handler);
#if defined(__linux__)
	signal(SIGHUP, SIGINT_handler);
#endif
	//set memory handler
	std::set_new_handler(noMoreMem);

	//set start time
	double cpu_time = cpuTime();

	//parse command-line options
	if(!parseOptions(argc, argv)){
		return 1;
	}

	//printMainStart(modes.verbosity);

	pData d;
	int returnvalue = 1;
	try { // Start catching IDP exceptions

		//IMPORTANT: because signals are handled asynchronously, a special mechanism is needed to recover from them (exception throwing does not work)
		//setjmp maintains a jump point to which any stack can jump back, re-executing this statement with different return value,
		//so if this happens, we jump out
		if(setjmp(main_loop)){
			char s[100];
			sprintf(s, "Signal handled: %s", mem==1?"out of memory":"execution interrupted");
			throw idpexception(s);
		}
		returnvalue = doModelGeneration(d, cpu_time);

#ifdef NDEBUG
		exit(returnvalue);     // (faster than "return", which will invoke the destructor for 'Solver')
#endif
	} catch (const idpexception& e) {
		//printExceptionCaught(e, modes.verbosity);
		if(d.get()!=NULL){
			d->printStatistics();
		}
	} catch (...) {
		//printUnexpectedError(modes.verbosity);
		if(d.get()!=NULL){
			d->printStatistics();
		}
	}

	return returnvalue;
}

int doModelGeneration(pData& d, double cpu_time){
	// Unittest injection possible by: pData d = unittestx();

	//Parse input
	switch(getChosenFormat()){
		case FORMAT_ASP:{
			WrappedPCSolver* p = new WrappedPCSolver(modes);
			d = shared_ptr<WrappedLogicSolver> (p);
			Read* r = new Read(p);
			std::filebuf buf;
			buf.open(MinisatID::getInputFileUrl(), std::ios::in);
			std::istream is(&buf);
			if(r->read(is)!=0){
				throw idpexception("Error in lparse parsing!");
			}
			buf.close();
			delete r;
			break;}
		case FORMAT_OPB:{
			WrappedPCSolver* p = new WrappedPCSolver(modes);
			d = shared_ptr<WrappedLogicSolver> (p);
			PBRead* parser = new PBRead(p, MinisatID::getInputFileUrl());
			parser->autoLin();
			parser->parse();
			delete parser;
			break;}
		case FORMAT_FODOT:{
			yyin = MinisatID::getInputFile();
			d = parse();
			break;}
	}

	MinisatID::closeInput();

	//d is initialized unless unsat was already detected
	bool unsat = d.get()==NULL;

	//printDataInitStart(modes.verbosity);

	//Initialize datastructures
	if(!unsat){
		unsat = !d->finishParsing();
	}

	if (modes.verbosity >= 2) {
		report("| Datastructure initialization finished                                       |\n");
		double parse_time = cpuTime() - cpu_time;
		report("| Total parsing time              : %7.2f s                                 |\n", parse_time);
	}

	if(modes.verbosity >= 1){
		report("===============================================================================\n");
		if (modes.verbosity >= 2) {
			if (unsat) {
				report("| Unsatisfiable found by parsing                                              |\n");
			}
		}
	}

	//Simplify
	if(!unsat){
		unsat = !d->simplify();
		if (modes.verbosity >= 1) {
			report("===============================================================================\n");
			if (modes.verbosity >= 2) {
				if (unsat) {
					report("| Unsatisfiable found by unit propagation                                     |\n");
				}
			}
		}
	}

	//Solve
	bool earlyunsat = unsat;
	if(!unsat){
		if (modes.verbosity >= 1) {
			report("| Solving                                                                     |\n");
		}
		vector<Literal> assumpts;
		Solution* sol = new Solution(modes.verbosity>0, false, true, modes.nbmodels, assumpts);
		unsat = !d->solve(sol);
		delete sol;
		if (modes.verbosity >= 1) {
			report("===============================================================================\n");
		}
	}

	if(unsat){
		fprintf(getOutputFile(), "UNSAT\n");
		if(modes.verbosity >= 1){
			report("UNSATISFIABLE\n");
		}
	}

	if(!earlyunsat && modes.verbosity >= 1){
		d->printStatistics();
	}

	MinisatID::closeOutput();

	return unsat ? 20 : 10;
}

///////
// PARSE CODE
///////

/**
 * Returns a data object representing the solver configuration from the input theory.
 * If the input theory was already found to be unsatisfiable, an empty shared pointer is returned.
 */
pData parse() {
	yyinit();

	try {
		/*ecnfparse();*/
		yyparse();
	} catch (const MinisatID::idpexception& e) {
		if (unsatfound) {
			std::cerr << "Unsat detected during parsing.\n";
		} else {
			//TODO this can also be caught when the sigint handler has received an interrupt, should differentiate
			char s[300];
			sprintf(s, "Parse error: Line %d, column %d, on \"%s\": %s", lineNo, charPos, yytext, e.what());
			throw idpexception(s);
		}
	}

	pData d = getData();

	yydestroy();
	//There is still a memory leak of about 16 Kb in the flex scanner, which is inherent to the flex C scanner

	if (unsatfound) { //UNSAT so empty shared pointer
		return shared_ptr<WrappedLogicSolver> ();
	}

	return d;
}

///////
// Debugging - information printing
///////

static void noMoreMem() {
	//Tries to reduce the memory of the solver by reducing the number of learned clauses
	//This keeps being called until enough memory is free or no more learned clauses can be deleted (causing abort).
	bool reducedmem = false;
	//TODO try to reduce solver clause base
	if (!reducedmem) {
		mem=1;
		longjmp (main_loop, 1);
	}
}

static void SIGINT_handler(int signum) {
	mem=0;
	longjmp (main_loop, 1);
}
