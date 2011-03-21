/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
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
volatile sig_atomic_t abortcode;
volatile sig_atomic_t memoryoverflow = 0;
static void SIGABRT_handler(int signum);
static void SIGFPE_handler(int signum);
static void SIGSEGV_handler(int signum);
static void SIGTERM_handler(int signum);
static void SIGINT_handler(int signum);
void handleSignals(int code, int& returnvalue, pwls data);

int doModelGeneration(pwls& d);

extern SolverOption modes;
FODOTTranslator* fodottrans;

Solution* sol = NULL;
Translator* trans = NULL;

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
		bool stoprunning = false;
		if(setjmp(main_loop)){
			handleSignals(abortcode, returnvalue, d);
			stoprunning = true;
		}
		if(!stoprunning){
			returnvalue = doModelGeneration(d);
		}

#ifdef NDEBUG
		exit(returnvalue);     // (faster than "return", which will invoke the destructor for 'Solver')
#endif
	} catch (const exception& e) {
		printExceptionCaught(cerr, e);
		if(d.get()!=NULL){
			printStatistics(d);
		}
		_exit(1);
	}

	if(trans!=NULL){
		delete trans;
	}

	if(sol!=NULL){
		delete sol;
	}

	return returnvalue;
}

bool initializeAndParseASP(pwls& d){
	bool unsat = false;

	WrappedPCSolver* p = new WrappedPCSolver(modes);
	d = shared_ptr<WrappedLogicSolver>(p);

	LParseTranslator* lptrans = new LParseTranslator();
	trans = lptrans;
	p->setTranslator(trans);

	Read* r = new Read(p, lptrans);

	std::istream is(getInputBuffer());
	if(!r->read(is)){
		unsat = true;
	}

	delete r;
	closeInput();

	return unsat;
}

bool initializeAndParseOPB(pwls& d){
	bool unsat = false;

	WrappedPCSolver* p = new WrappedPCSolver(modes);
	d = shared_ptr<WrappedLogicSolver>(p); //Only set d if successfully parsed

	OPBTranslator* opbtrans = new OPBTranslator();
	trans = opbtrans;
	p->setTranslator(trans);

	std::istream is(getInputBuffer());

	PBRead* parser = new PBRead(p, opbtrans, is);
	parser->autoLin();

	parser->parse();

	closeInput();
	delete parser;

	return unsat;
}

bool initializeAndParseFODOT(pwls& d){
	if(modes.transformat!=TRANS_PLAIN){
		fodottrans = new FODOTTranslator(modes.transformat);
		trans = fodottrans;
	}

	yyin = getInputFile();
	d = parse();
	closeInput();

	return d.get()==NULL;
}

int doModelGeneration(pwls& d){
	// Unittest injection possible here by: pwls d = unittestx();

	bool unsat = false;
	switch(modes.format){
		case FORMAT_ASP:
			unsat = initializeAndParseASP(d);
			break;
		case FORMAT_OPB:
			unsat = initializeAndParseOPB(d);
			break;
		case FORMAT_FODOT:{
			unsat = initializeAndParseFODOT(d);
			break;
		}
	}

	if(unsat){
		ostream output(getOutputBuffer());
		printUnSatisfiable(output, modes.format, modes.transformat);
		printUnSatisfiable(clog, modes.format, modes.transformat, modes.verbosity);
	}else{ //Solve
		ModelExpandOptions options;
		if(modes.format==FORMAT_OPB && d->hasOptimization()){
			options.printmodels	= PRINT_BEST;
			options.savemodels = SAVE_BEST;
		}else{
			options.printmodels	= PRINT_ALL;
			options.savemodels = SAVE_NONE;
		}
		options.search = MODELEXPAND;
		options.nbmodelstofind = modes.nbmodels;
		sol = new Solution(options);
		unsat = !d->solve(sol);

		printStatistics(d, modes.verbosity);
	}

	return unsat ? 20 : 10;
}

/**
 * Returns a data object representing the solver configuration from the input theory.
 * If the input theory was already found to be unsatisfiable, an empty shared pointer is returned.
 */
pwls parse() {
	yyinit();

	try {
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

	yydestroy(); //There is still a memory leak of about 16 Kb in the flex scanner, which is inherent to the flex C (not C++) scanner

	if (unsatfound) {
		d = shared_ptr<WrappedLogicSolver> ();
	}

	return d;
}

// Debugging - information printing

static void noMoreMem() {
	//Tries to reduce the memory of the solver by reducing the number of learned clauses
	//This keeps being called until enough memory is free or no more learned clauses can be deleted (causing abort).
	bool reducedmem = false;
	//TODO try to reduce solver clause base
	if (!reducedmem) {
		abortcode=SIGINT;
		memoryoverflow = 1;
		longjmp (main_loop, 1);
	}
}

static void SIGFPE_handler(int signum) {
	abortcode = SIGFPE;
	longjmp (main_loop, 1);
}

//IMPORTANT: assumed this is always called externally
static void SIGTERM_handler(int signum) {
	abortcode = SIGTERM;
	longjmp (main_loop, 1);
}

static void SIGABRT_handler(int signum) {
	abortcode=SIGABRT;
	longjmp (main_loop, 1);
}

static void SIGSEGV_handler(int signum) {
	abortcode=SIGSEGV;
	longjmp (main_loop, 1);
}

static void SIGINT_handler(int signum) {
	abortcode=SIGINT;
	longjmp (main_loop, 1);
}

void handleSignals(int code, int& returnvalue, pwls d){
	bool cleanexit = false;

	switch(abortcode){
	case SIGFPE:
		cerr <<">>> Floating point error signal received\n";
		break;
	case SIGABRT:
		cerr <<">>> Abort signal received\n";
		break;
	case SIGINT:
		clog <<">>> Ctrl-c signal received\n";
		cleanexit = true;
		break;
	case SIGSEGV:
		cerr <<">>> Segmentation fault signal received\n";
		break;
	case SIGTERM:
		clog <<">>> Terminate signal received\n";
		cleanexit = true;
		break;
	}

	if(cleanexit){
		returnvalue = 0;
		if(d.get()!=NULL){
			d->notifyTimeout();
		}
	}else{
		returnvalue = abortcode;
		if(memoryoverflow==1){
			throw idpexception(">>> Signal handled: out of memory\n");
		}else{
			throw idpexception(">>> Signal handled: execution interrupted\n");
		}
	}
}
