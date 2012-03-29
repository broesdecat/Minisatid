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
#include <cstdint>
#include <cerrno>
#include <iostream>
#include <fstream>
#include <csignal>
#include <sstream>

#include "parser/CommandLineOptions.hpp"
#include "external/DataAndInference.hpp"

#include <csetjmp>

#include "external/Translator.hpp"
#include "external/SolvingMonitor.hpp"
#include "utils/ResourceManager.hpp"
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

typedef Space* pwls;

extern char* yytext;
extern int lineNo;
extern int charPos;
extern void setSpace(pwls);

extern FILE* yyin;
extern int yyparse();
extern void yydestroy();
extern void yyinit();
extern bool unsatfound;

void parse(pwls d);

jmp_buf main_loop;
static void noMoreMem();
volatile sig_atomic_t abortcode;
volatile sig_atomic_t jumpback; //Only jump back when this is 0
static void SIGABRT_handler(int signum);
static void SIGFPE_handler(int signum);
static void SIGSEGV_handler(int signum);
static void SIGTERM_handler(int signum);
static void SIGINT_handler(int signum);
void handleSignals();

void parseAndInitializeTheory(pwls d);
void doModelGeneration(pwls d);

void rewriteIntoFlatZinc();

extern SolverOption modes;
OutputFormat transformat;

Solution* sol = NULL;

Solution* createSolution() {
	ModelExpandOptions options;
	options.printmodels = Models::BEST;
	options.savemodels = Models::NONE;
	options.inference = Inference::MODELEXPAND;
	options.nbmodelstofind = 1;
	return new Solution(options);
}

int handleTermination(bool cleanexit, pwls d) {
	if (!cleanexit) {
		sol->notifySolvingAborted();
	}
	int returnvalue = 0;
	if (sol->isUnsat()) {
		returnvalue = 20;
	} else {
		if (sol->isSat()) {
			returnvalue = 10;
		}
	}

	if (d != NULL && modes.verbosity > 1) {
		//TODO d->printStatistics();
	}
	return returnvalue;
}

int main(int argc, char** argv) {
	//Setting system precision and signal handlers
#if defined(__linux__)
	fpu_control_t oldcw, newcw;
	_FPU_GETCW(oldcw);
	newcw = (oldcw & ~_FPU_EXTENDED) | _FPU_DOUBLE;
	_FPU_SETCW(newcw);
	// double precision for repeatability
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
	if (!successfullparsing) {
		sol->notifySolvingAborted();
		return 0;
	} else {
		sol->setNbModelsToFind(modes.nbmodels);
	}
	sol->setModes(modes); //TODO find cleaner way? => these are set when solve is called, but earlier statements might have incorrect behavior then (printing unsat e.g.)
	sol->setInference(modes.inference);

	if (modes.transformat == OutputFormat::FZ) {
		rewriteIntoFlatZinc();
		return 0;
	}

	printMainStart(modes.verbosity);

	pwls d = new Space(modes);
	bool cleanexit = false;
#ifdef NDEBUG
	try {
#endif
		//IMPORTANT: because signals are handled asynchronously, a special mechanism is needed to recover from them (exception throwing does not work)
		//setjmp maintains a jump point to which any stack can jump back, re-executing this statement with different return value,
		//so if this happens, we jump out
		bool stoprunning = false;
		if (setjmp(main_loop)) {
			jumpback = 1;
			handleSignals();
			cleanexit = false;
			stoprunning = true;
		}
		if (!stoprunning) {
			jumpback = 0;
			parseAndInitializeTheory(d);
			if (sol->getInferenceOption() == Inference::MODELEXPAND || sol->getInferenceOption() == Inference::PROPAGATE) {
				doModelGeneration(d);
			} else if (sol->getInferenceOption() == Inference::PRINTTHEORY) {
				// Do unit propagation
				sol->setInferenceOption(Inference::PROPAGATE);
				sol->setPrintModels(Models::NONE);
				doModelGeneration(d);

				// Print the theory
				sol->setInferenceOption(Inference::PRINTTHEORY);
				if (sol->isUnsat()) {
					cout << "p ecnf\n0\n";
					cout.flush();
				} else {
					assert(d!=NULL);
					// TODO d->printTheory(cout);
					cout.flush();
				}
			}

			jumpback = 1;
			cleanexit = true;
		}
#ifdef NDEBUG
	} catch (const exception& e) {
		printExceptionCaught(clog, e);
		cleanexit = false;
	} catch (int i) {
		printUnexpectedError(clog);
		cleanexit = false;
	}
#endif
	jumpback = 1;

	int returnvalue = handleTermination(cleanexit, d);

#ifdef NDEBUG
	return returnvalue; //Do not call all destructors
#endif

	if (sol != NULL) {
		delete sol;
	}
	if (d != NULL) {
		delete (d);
	}

	return returnvalue;
}

void rewriteIntoFlatZinc() {
	// FIXME
	/*	switch (modes.format) {
	 case InputFormat::ASP: {
	 LParseTranslator* lptrans = new LParseTranslator();
	 sol->setTranslator(lptrans);

	 std::istream is(getInputBuffer());
	 FlatZincRewriter* p = new FlatZincRewriter(modes);
	 Read<FlatZincRewriter>* r = new Read<FlatZincRewriter>(p, lptrans);
	 r->read(is);
	 delete r;
	 closeInput();
	 p->finishParsing();
	 break;
	 }
	 case InputFormat::OPB: {
	 OPBTranslator* opbtrans = new OPBTranslator();
	 sol->setTranslator(opbtrans);

	 std::istream is(getInputBuffer());
	 FlatZincRewriter* p = new FlatZincRewriter(modes);
	 PBRead<FlatZincRewriter>* r = new PBRead<FlatZincRewriter>(p, opbtrans, is);
	 r->parse();
	 delete r;
	 closeInput();
	 p->finishParsing();
	 break;
	 }
	 case InputFormat::FODOT: {
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
	 }*/
}

void initializeAndParseASP(pwls d) {
	LParseTranslator* lptrans = new LParseTranslator();
	if (modes.transformat != OutputFormat::PLAIN) {
		sol->setTranslator(lptrans);
	}

	std::istream is(getInputBuffer());
	auto r = new Read<Space>(*d, lptrans);

	r->read(is);
	closeInput();
	delete r;
}

void initializeAndParseOPB(pwls d) {
	OPBTranslator* opbtrans = new OPBTranslator();
	if (modes.transformat != OutputFormat::PLAIN) {
		sol->setTranslator(opbtrans);
	}

	std::istream is(getInputBuffer());
	auto parser = new PBRead<Space>(*d, opbtrans, is);

	parser->parse();
	closeInput();
	delete parser;

	if (modes.transformat == OutputFormat::PLAIN) {
		delete (opbtrans);
	}
}

void initializeAndParseFODOT(pwls d) {
	if (modes.transformat != OutputFormat::PLAIN) {
		transformat = modes.transformat;
	}

	yyin = getInputFile();
	parse(d);
	closeInput();
}

void parseAndInitializeTheory(pwls d) {
	sol->notifyStartParsing();

	switch (modes.format) {
	case InputFormat::ASP:
		initializeAndParseASP(d);
		break;
	case InputFormat::OPB:
		initializeAndParseOPB(d);
		break;
	case InputFormat::FODOT: {
		initializeAndParseFODOT(d);
		break;
	}
	}

	if (d->isCertainlyUnsat()) {
		sol->notifyUnsat();
	}

	sol->notifyEndParsing();
}

void doModelGeneration(pwls d) {
	if (sol->isUnsat()) {
		sol->notifySolvingFinished();
		return;
	}

	assert(d!=NULL);
	// FIXME need to move optimization to lower than ModelExpand Task, because cannot add to inference during parsing!!!

	// TODO
	//if (d->hasOptimization()) {
	//	sol->notifyOptimizing();
	//}

	if (modes.format == InputFormat::OPB && sol->isOptimizationProblem()) { // Change default options added before parsing
		sol->setPrintModels(Models::BEST);
		sol->setSaveModels(Models::BEST);
	}

	auto mx = ModelExpand(d, sol->getOptions()); // FIXME remove sol from main
	mx.execute();
}

/**
 * Returns a data object representing the solver configuration from the input theory.
 * If the input theory was already found to be unsatisfiable, an empty shared pointer is returned.
 */
void parse(pwls d) {
	yyinit();

	setSpace(d);

	try {
		yyparse();
	} catch (const MinisatID::idpexception& e) {
		if (unsatfound) {
			printUnsatFoundDuringParsing(clog, modes.verbosity);
		} else {
			throw idpexception(getParseError(e, lineNo, charPos, yytext));
		}
	}

	yydestroy();

	if (unsatfound) {
		sol->notifyUnsat();
		delete (d);
		d = NULL;
	}
}

// Debugging - information printing

static void noMoreMem() {
	//Tries to reduce the memory of the solver by reducing the number of learned clauses
	//This keeps being called until enough memory is free or no more learned clauses can be deleted (causing abort).
	bool reducedmem = false;
	//TODO try to reduce solver clause base
	if (!reducedmem) {
		abortcode = SIGABRT;
		clog << ">>> Signal handled: out of memory\n";
		longjmp(main_loop, 1);
	}
}

static void SIGFPE_handler(int) {
	abortcode = SIGFPE;
	if (jumpback == 0) {
		longjmp(main_loop, 1);
	}
}

//IMPORTANT: assumed this is always called externally
static void SIGTERM_handler(int) {
	abortcode = SIGTERM;
	if (jumpback == 0) {
		longjmp(main_loop, 1);
	}
}

static void SIGABRT_handler(int) {
	abortcode = SIGABRT;
	if (jumpback == 0) {
		longjmp(main_loop, 1);
	}
}

static void SIGSEGV_handler(int) {
	abortcode = SIGSEGV;
	if (jumpback == 0) {
		longjmp(main_loop, 1);
	}
}

static void SIGINT_handler(int) {
	abortcode = SIGINT;
	if (jumpback == 0) {
		longjmp(main_loop, 1);
	}
}

void handleSignals() {
	switch (abortcode) {
	case SIGFPE:
		clog << ">>> Floating point error signal received\n";
		break;
	case SIGABRT:
		clog << ">>> Abort signal received\n";
		break;
	case SIGINT:
		clog << ">>> Ctrl-c signal received\n";
		break;
	case SIGSEGV:
		clog << ">>> Segmentation fault signal received\n";
		break;
	case SIGTERM:
		clog << ">>> Terminate signal received\n";
		break;
	}
}
