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
static void SIGABRT_handler(int signum);
static void SIGFPE_handler(int signum);
static void SIGSEGV_handler(int signum);
static void SIGTERM_handler(int signum);
static void SIGINT_handler(int signum);
void handleSignals();
int handleTermination(pwls d);

void doModelGeneration(pwls& d);

extern SolverOption modes;
FODOTTranslator* fodottrans;

Solution* sol = NULL;
Translator* trans = NULL;

Solution* createSolution(){
	ModelExpandOptions options;
	options.printmodels	= PRINT_ALL;
	options.savemodels = SAVE_NONE;
	options.search = MODELEXPAND;
	options.nbmodelstofind = 1;
	return new Solution(options);
}

int handleTermination(bool cleanexit, pwls d){
    if(cleanexit){
        sol->notifyEndSolving();
    }else{
        sol->notifySolvingAborted();
    }
    int returnvalue = 0;
    if(sol->isUnsat()){
        returnvalue = 20;
    }else
        if(sol->isSat()){
            returnvalue = 10;
        }

    if(d.get()!=NULL && modes.verbosity>0){
		printStatistics(d);
	}
    return returnvalue;
}

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

	sol = createSolution();

	//parse command-line options
	bool successfullparsing = parseOptions(argc, argv);
	if(!successfullparsing){
		sol->notifySolvingAborted();
		return 0;
	}else{
		sol->setOutputResourceManager(getOutputResMan());
		sol->setNbModelsToFind(modes.nbmodels);
	}

	printMainStart(modes.verbosity);

	pwls d;
	bool cleanexit = false;
	try {
		//IMPORTANT: because signals are handled asynchronously, a special mechanism is needed to recover from them (exception throwing does not work)
		//setjmp maintains a jump point to which any stack can jump back, re-executing this statement with different return value,
		//so if this happens, we jump out
		bool stoprunning = false;
		if(setjmp(main_loop)){
			handleSignals();
			cleanexit = false;
			stoprunning = true;
		}
		if(!stoprunning){
			doModelGeneration(d);
			cleanexit = true;
		}
	} catch (const exception& e) {
		printExceptionCaught(cerr, e);
		cleanexit = false;
	} catch (int i) {
		printUnexpectedError(cerr);
		cleanexit = false;
	}

	int returnvalue = handleTermination(cleanexit, d);

#ifdef NDEBUG
		exit(returnvalue);     // (faster than "return", which will invoke the destructors)
#endif

	if(trans!=NULL){
		delete trans;
	}

	if(sol!=NULL){
		delete sol;
	}

	return returnvalue;
}

void initializeAndParseASP(pwls& d){
	WrappedPCSolver* p = new WrappedPCSolver(modes);
	d = shared_ptr<WrappedLogicSolver>(p);

	LParseTranslator* lptrans = new LParseTranslator();
	trans = lptrans;
	sol->setTranslator(trans);

	Read* r = new Read(p, lptrans);

	std::istream is(getInputBuffer());
	if(!r->read(is)){
		sol->notifyUnsat();
	}

	delete r;
	closeInput();
}

void initializeAndParseOPB(pwls& d){
	WrappedPCSolver* p = new WrappedPCSolver(modes);
	d = shared_ptr<WrappedLogicSolver>(p); //Only set d if successfully parsed

	OPBTranslator* opbtrans = new OPBTranslator();
	trans = opbtrans;
	sol->setTranslator(trans);

	std::istream is(getInputBuffer());

	PBRead* parser = new PBRead(p, opbtrans, is);
	parser->autoLin();

	parser->parse();

	closeInput();
	delete parser;
}

void initializeAndParseFODOT(pwls& d){
	if(modes.transformat!=TRANS_PLAIN){
		fodottrans = new FODOTTranslator(modes.transformat);
		trans = fodottrans;
	}

	yyin = getInputFile();
	d = parse();
	closeInput();
}

void doModelGeneration(pwls& d){
	// Unittest injection possible here by: pwls d = unittestx();

	sol->notifyStartParsing();

	switch(modes.format){
		case FORMAT_ASP:
			initializeAndParseASP(d);
			break;
		case FORMAT_OPB:
			initializeAndParseOPB(d);
			break;
		case FORMAT_FODOT:{
			initializeAndParseFODOT(d);
			break;
		}
	}

	sol->notifyEndParsing();

	if(modes.format==FORMAT_OPB && d->hasOptimization()){ // Change default options added before parsing
		sol->setPrintModels(PRINT_BEST);
		sol->setSaveModels(SAVE_BEST);
	}

	if(!sol->isUnsat()){
		d->solve(sol);
	}
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

	yydestroy();

	if (unsatfound) {
		sol->notifyUnsat();
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
		clog <<">>> Signal handled: out of memory\n";
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

void handleSignals(){
	switch(abortcode){
	case SIGFPE:
		cerr <<">>> Floating point error signal received\n";
		break;
	case SIGABRT:
		cerr <<">>> Abort signal received\n";
		break;
	case SIGINT:
		clog <<">>> Ctrl-c signal received\n";
		break;
	case SIGSEGV:
		cerr <<">>> Segmentation fault signal received\n";
		break;
	case SIGTERM:
		clog <<">>> Terminate signal received\n";
		break;
	}
}
