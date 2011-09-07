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
#include "external/FlatZincRewriter.hpp"
#include "external/Translator.hpp"
#include "Unittests.hpp"
#include "external/ResourceManager.hpp"
#include "parser/Lparseread.hpp"
#include "parser/PBread.hpp"

#include "utils/Print.hpp"

#if defined(__linux__)
#include <fpu_control.h>
#endif

using namespace std;
using namespace MinisatID;

#include "parser/Lparseread.cpp"
#include "parser/PBread.cpp"

extern char* 	yytext;
extern int 		lineNo;
extern int 		charPos;
extern pwls 	getData();
extern FlatZincRewriter* getFZRewriter();

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
volatile sig_atomic_t jumpback;	//Only jump back when this is 0
static void SIGABRT_handler	(int signum);
static void SIGFPE_handler	(int signum);
static void SIGSEGV_handler	(int signum);
static void SIGTERM_handler	(int signum);
static void SIGINT_handler	(int signum);
void handleSignals	();
int handleTermination(pwls d);

void parseAndInitializeTheory(pwls& d);
void doModelGeneration(pwls& d);

void rewriteIntoFlatZinc();

extern SolverOption modes;
OUTPUTFORMAT transformat;

Solution* sol = NULL;

Solution* createSolution(){
	ModelExpandOptions options;
	options.printmodels	= PRINT_BEST;
	options.savemodels = SAVE_NONE;
	options.search = MODELEXPAND;
	options.nbmodelstofind = 1;
	return new Solution(options);
}

int handleTermination(bool cleanexit, pwls d){
    if(!cleanexit){
        sol->notifySolvingAborted();
    }
    int returnvalue = 0;
    if(sol->isUnsat()){
        returnvalue = 20;
    }else{
        if(sol->isSat()){
            returnvalue = 10;
        }
    }

    if(d!=NULL && modes.verbosity>1){
    	d->printStatistics();
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

	jumpback = 1;
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
	bool successfullparsing = parseOptions(argc, argv, sol);
	if(!successfullparsing){
		sol->notifySolvingAborted();
		return 0;
	}else{
		sol->setNbModelsToFind(modes.nbmodels);
	}
	sol->setModes(modes); //TODO find cleaner way? => these are set when solve is called, but earlier statements might have incorrect behavior then (printing unsat e.g.)
	sol->setInference(modes.inference);

	if(modes.transformat==TRANS_FZ){
		rewriteIntoFlatZinc();
		return 0;
	}

	printMainStart(modes.verbosity);

	pwls d = NULL;
	bool cleanexit = false;
#ifdef NDEBUG
	try {
#endif
		//IMPORTANT: because signals are handled asynchronously, a special mechanism is needed to recover from them (exception throwing does not work)
		//setjmp maintains a jump point to which any stack can jump back, re-executing this statement with different return value,
		//so if this happens, we jump out
		bool stoprunning = false;
		if(setjmp(main_loop)){
			jumpback = 1;
			handleSignals();
			cleanexit = false;
			stoprunning = true;
		}
		if(!stoprunning){
			jumpback = 0;
			parseAndInitializeTheory(d);
			if(sol->getInferenceOption()==MODELEXPAND){
				doModelGeneration(d);
			}else if(sol->getInferenceOption()==PRINTTHEORY){
				if(sol->isUnsat()){
					cout <<"p ecnf\n0\n"; cout.flush();
				}else{
					assert(d!=NULL);
					d->printTheory(cout, sol);
					cout.flush();
				}
			}

			jumpback = 1;
			cleanexit = true;
		}
#ifdef NDEBUG
	} catch (const exception& e) {
		printExceptionCaught(cerr, e);
		cleanexit = false;
	} catch (int i) {
		printUnexpectedError(cerr);
		cleanexit = false;
	}
#endif
	jumpback = 1;

	int returnvalue = handleTermination(cleanexit, d);

#ifdef NDEBUG
	return returnvalue; //Do not call all destructors
#endif

	if(sol!=NULL){
		delete sol;
	}

	if(d!=NULL){
		delete d;
	}
	return returnvalue;
}

void rewriteIntoFlatZinc(){
	switch(modes.format){
		case FORMAT_ASP:{
			LParseTranslator* lptrans = new LParseTranslator();
			sol->setTranslator(lptrans);

			std::istream is(getInputBuffer());
			FlatZincRewriter* p = new FlatZincRewriter(modes);
			Read<FlatZincRewriter>* r = new Read<FlatZincRewriter>(p, lptrans);
			r->read(is);
			delete r;
			closeInput();
			p->finishParsing();
			break;}
		case FORMAT_OPB:{
			OPBTranslator* opbtrans = new OPBTranslator();
			sol->setTranslator(opbtrans);

			std::istream is(getInputBuffer());
			FlatZincRewriter* p = new FlatZincRewriter(modes);
			PBRead<FlatZincRewriter>* r = new PBRead<FlatZincRewriter>(p, opbtrans, is);
			r->parse();
			delete r;
			closeInput();
			p->finishParsing();
			break;}
		case FORMAT_FODOT:{
			yyin = getInputFile();
			yyinit();
			try {
				yyparse();
			} catch (const MinisatID::idpexception& e) {
				throw idpexception(getParseError(e, lineNo, charPos, yytext));
			}
			yydestroy();
			closeInput();
			getFZRewriter()->finishParsing();
			break;
		}
	}
}

pwls initializeAndParseASP(){
	LParseTranslator* lptrans = new LParseTranslator();
	if(modes.transformat!=TRANS_PLAIN){
		sol->setTranslator(lptrans);
	}

	std::istream is(getInputBuffer());
	WrappedPCSolver* p = new WrappedPCSolver(modes);
	Read<WrappedPCSolver>* r = new Read<WrappedPCSolver>(p, lptrans);

	if(!r->read(is)){
		sol->notifyUnsat();
	}
	closeInput();
	delete r;

	return p;
}

pwls initializeAndParseOPB(){
	OPBTranslator* opbtrans = new OPBTranslator();
	if(modes.transformat!=TRANS_PLAIN){
		sol->setTranslator(opbtrans);
	}

	std::istream is(getInputBuffer());
	WrappedPCSolver* p = new WrappedPCSolver(modes);
	PBRead<WrappedPCSolver>* parser = new PBRead<WrappedPCSolver>(p, opbtrans, is);

	if(!parser->parse()){
		sol->notifyUnsat();
	}
	closeInput();
	delete parser;

	if(modes.transformat==TRANS_PLAIN){
		delete(opbtrans);
	}

	return p;
}

pwls initializeAndParseFODOT(){
	if(modes.transformat!=TRANS_PLAIN){
		transformat = modes.transformat;
	}

	yyin = getInputFile();
	pwls d = parse();
	closeInput();
	return d;
}

void parseAndInitializeTheory(pwls& d){
	sol->notifyStartParsing();

	switch(modes.format){
		case FORMAT_ASP:
			d = initializeAndParseASP();
			break;
		case FORMAT_OPB:
			d = initializeAndParseOPB();
			break;
		case FORMAT_FODOT:{
			d = initializeAndParseFODOT();
			break;
		}
	}

	sol->notifyEndParsing();
}

void doModelGeneration(pwls& d){
	// Unittest injection possible here by: pwls d = unittestx();

	if(!sol->isUnsat()){
		assert(d!=NULL);
		if(d->hasOptimization()){
			sol->notifyOptimizing();
		}

		if(modes.format==FORMAT_OPB && sol->isOptimizationProblem()){ // Change default options added before parsing
			sol->setPrintModels(PRINT_BEST);
			sol->setSaveModels(SAVE_BEST);
		}

		d->solve(sol);
	}else{
		sol->notifySolvingFinished();
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
			throw idpexception(getParseError(e, lineNo, charPos, yytext));
		}
	}

	pwls d = getData();

	yydestroy();

	if (unsatfound) {
		sol->notifyUnsat();
		if(d!=NULL){
			delete d;
		}
		d = NULL;
	}else{
		assert(d!=NULL);
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
		abortcode=SIGABRT;
		clog <<">>> Signal handled: out of memory\n";
		longjmp (main_loop, 1);
	}
}

static void SIGFPE_handler(int signum) {
	abortcode = SIGFPE;
	if(jumpback==0){
		longjmp (main_loop, 1);
	}
}

//IMPORTANT: assumed this is always called externally
static void SIGTERM_handler(int signum) {
	abortcode = SIGTERM;
	if(jumpback==0){
		longjmp (main_loop, 1);
	}
}

static void SIGABRT_handler(int signum) {
	abortcode=SIGABRT;
	if(jumpback==0){
		longjmp (main_loop, 1);
	}
}

static void SIGSEGV_handler(int signum) {
	abortcode=SIGSEGV;
	if(jumpback==0){
		longjmp (main_loop, 1);
	}
}

static void SIGINT_handler(int signum) {
	abortcode=SIGINT;
	if(jumpback==0){
		longjmp (main_loop, 1);
	}
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
