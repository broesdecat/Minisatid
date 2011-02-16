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

//------------------------------------------------------------------------------
// Copyright (c) 2006-2009, Maarten Mariën

// Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
// associated documentation files (the "Software"), to deal in the Software without restriction,
// including without limitation the rights to use, copy, modify, merge, publish, distribute,
// sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:

// The above copyright notice and this permission notice shall be included in all copies or
// substantial portions of the Software.

// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
// NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
// NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
// DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
// OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
//------------------------------------------------------------------------------

#include <ctime>
#include <cstring>
#include <stdint.h>
#include <cerrno>
#include <iostream>
#include <fstream>
#include <signal.h>
#include <sstream>

#include "parser/ParseOptions.hpp"

#include <setjmp.h>

#include "external/ExternalInterface.hpp"
#include "external/Translator.hpp"
#include "Unittests.hpp"
#include "parser/ResourceManager.hpp"
#include "parser/Lparseread.hpp"
#include "parser/PBread.hpp"

#include "utils/Print.hpp"

#if defined(__linux__)
#include <fpu_control.h>
#endif

using namespace std;
#ifndef __GXX_EXPERIMENTAL_CXX0X__
using namespace std::tr1;
#endif
using namespace MinisatID;
using namespace MinisatID::Print;

extern char* 	yytext;
extern int 		lineNo;
extern int 		charPos;
extern pwls 	getData();

extern FILE* 	yyin;
extern int 		yyparse();
extern void 	yydestroy();
extern void 	yyinit();
extern bool 	unsatfound;

const char* 	hasPrefix(const char* str, const char* prefix);
pwls parse();

void printStats();

jmp_buf main_loop;
static void noMoreMem();
volatile sig_atomic_t mem;
static void SIGABRT_handler(int signum);
static void SIGFPE_handler(int signum);
static void SIGSEGV_handler(int signum);
static void SIGTERM_handler(int signum);
static void SIGINT_handler(int signum);


int doModelGeneration(pwls& d);

extern SolverOption modes;
FODOTTranslator* fodottrans;

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

	signal(SIGABRT, SIGABRT_handler);
	signal(SIGFPE, SIGFPE_handler);
	signal(SIGTERM, SIGTERM_handler);
	signal(SIGSEGV, SIGSEGV_handler);
	signal(SIGINT, SIGINT_handler);
#if defined(__linux__)
	signal(SIGHUP, SIGINT_handler);
#endif
	//set memory handler
	std::set_new_handler(noMoreMem);

	//parse command-line options
	if(!parseOptions(argc, argv)){
		return 1;
	}

	printMainStart(modes.verbosity);

	pwls d;
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
		returnvalue = doModelGeneration(d);

#ifdef NDEBUG
		exit(returnvalue);     // (faster than "return", which will invoke the destructor for 'Solver')
#endif
	} catch (const exception& e) {
		printExceptionCaught(cerr, e);
		if(d.get()!=NULL){
			printStatistics(d);
		}
		_exit(1);
	}/* catch (...) {
		printUnexpectedError(cerr);
		if(d.get()!=NULL){
			printStatistics(d);
		}
		_exit(1);
	}*/

	return returnvalue;
}

int doModelGeneration(pwls& d){
	// Unittest injection possible by: pwls d = unittestx();

	bool unsat = false;

	Translator* trans = NULL;

	//Parse input
	switch(modes.format){
		case FORMAT_ASP:{
			WrappedPCSolver* p = new WrappedPCSolver(modes);
			trans = new LParseTranslator();
			LParseTranslator& lptrans = *dynamic_cast<LParseTranslator*>(trans);
			p->setTranslator(lptrans);
			Read* r = new Read(p, lptrans);
			std::istream is(getInputBuffer());
			if(!r->read(is)){
				unsat = true;
			}else{
				d = shared_ptr<WrappedLogicSolver> (p); //Only set d if successfully parsed
			}
			closeInput();
			delete r;
			break;
		}
		case FORMAT_OPB:{
			WrappedPCSolver* p = new WrappedPCSolver(modes);
			std::istream is(getInputBuffer());
			PBRead* parser = new PBRead(p, is);
			parser->autoLin();
			parser->parse();
			closeInput();
			delete parser;
			d = shared_ptr<WrappedLogicSolver> (p); //Only set d if successfully parsed
			break;
		}
		case FORMAT_FODOT:{
			if(modes.transformat!=TRANS_PLAIN){
				fodottrans = new FODOTTranslator(modes.transformat);
				trans = fodottrans;
			}
			yyin = MinisatID::getInputFile();
			d = parse();
			break;
		}
	}

	MinisatID::closeInput();

	//d is initialized unless unsat was already detected
	unsat = unsat || d.get()==NULL;

	//Initialize datastructures
	if(!unsat){
		unsat = !d->finishParsing();
	}

	//Simplify
	if(!unsat){
		unsat = !d->simplify();
	}

	//Solve
	bool earlyunsat = unsat;
	if(!unsat){
		vector<Literal> assumpts;
		Solution* sol = new Solution(true, false, true, modes.nbmodels, assumpts);
		unsat = !d->solve(sol);
		delete sol;
	}

	std::ostream output(getOutputBuffer());
	if(unsat){
		printUnSatisfiable(output, modes.aspcomp3type);
		printUnSatisfiable(clog, modes.aspcomp3type, modes.verbosity);
	}

	if(!earlyunsat){
		printStatistics(d, modes.verbosity);
	}

	if(trans!=NULL){
		delete trans;
	}

	return unsat ? 20 : 10;
}

///////
// PARSE CODE
///////

/**
 * Returns a data object representing the solver configuration from the input theory.
 * If the input theory was already found to be unsatisfiable, an empty shared pointer is returned.
 */
pwls parse() {
	yyinit();

	try {
		/*ecnfparse();*/
		yyparse();
	} catch (const MinisatID::idpexception& e) {
		if (unsatfound) {
			printUnsatFoundDuringParsing(clog, modes.verbosity);
		} else {
			//TODO this can also be caught when the sigint handler has received an interrupt, should differentiate
			throw idpexception(getParseError(e, lineNo, charPos, yytext));
		}
	}

	pwls d = getData();

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

static void SIGABRT_handler(int signum) {
	cerr <<">>>Abort signal received\n";
	mem=0;
	longjmp (main_loop, 1);
}
static void SIGFPE_handler(int signum) {
	cerr <<">>> Floating point error signal received\n";
	mem=0;
	longjmp (main_loop, 1);
}
static void SIGTERM_handler(int signum) {
	cerr <<">>>Terminate signal received\n";
	mem=0;
	longjmp (main_loop, 1);
}
static void SIGSEGV_handler(int signum) {
	cerr <<">>>Segmentation fault signal received\n";
	mem=0;
	longjmp (main_loop, 1);
}
static void SIGINT_handler(int signum) {
	cerr <<">>>Integer error code signal received\n";
	mem=0;
	longjmp (main_loop, 1);
}
