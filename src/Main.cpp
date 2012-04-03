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
#include "inferences/Tasks.hpp"
#include "utils/TimingUtils.hpp"

#include <csetjmp>

#include "external/Translator.hpp"
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

ModelExpand* mx = NULL;

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

	//parse command-line options
	SolverOption modes;
	bool successfullparsing = parseOptions(argc, argv, modes);
	if (not successfullparsing) {
		clog << ">>> Error during parsing of command-line options, aborting...";
		return 0;
	}

	printMainStart(modes.verbosity);

	pwls d = new Space(modes);
	bool cleanexit = false;
	try {
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
			if (modes.inference == Inference::MODELEXPAND) {
				doModelGeneration(d);
			} else if (modes.inference == Inference::PROPAGATE) {
				auto up = UnitPropagate(d, {});
				up.execute();
				up.writeOutEntailedLiterals();
			} else if (modes.inference == Inference::PRINTTHEORY) {
				auto tp = TheoryPrinting::ECNF;
				switch(modes.transformat){
				case OutputFormat::FZ:
					tp = TheoryPrinting::FZ;
					break;
				case OutputFormat::PLAIN:
					tp = TheoryPrinting::HUMAN;
					break;
				case OutputFormat::FODOT:
					tp = TheoryPrinting::ECNF;
					break;
				default:
					throw notYetImplemented("Cannot print the theory in ASP.\n");
				}
				auto t = new Transform(d, tp);
				t->execute();
				delete(t);
			} else if (modes.inference == Inference::PRINTGRAPH) {
				auto t = new Transform(d, TheoryPrinting::ECNFGRAPH);
				t->execute();
				delete(t);
			}

			jumpback = 1;
			cleanexit = true;
		}
	} catch (const exception& e) {
		printExceptionCaught(clog, e);
		cleanexit = false;
	} catch (int i) {
		printUnexpectedError(clog);
		cleanexit = false;
	}
	jumpback = 1;

	int returnvalue = 0;
	if (not cleanexit) {
		returnvalue = -1;
	}
	if (mx != NULL) {
		if (not cleanexit) {
			// NOTE: if solving was aborted, more information might be available that has not been printed, so can be printed now.
			// for that, need to save mx ofcourse
			mx->notifySolvingAborted();
		}
		if (mx->isUnsat()) {
			returnvalue = 20;
		} else if (mx->isSat()) {
			returnvalue = 10;
		}
		delete (mx);
	}

	if (d != NULL) {
		if (d->getOptions().verbosity > 1) {
			// TODO auto transform = Transform(d, TheoryPrinting::STATS, clog); // Is NOT a constraintvisitor, but a propagatorvisitor!
			// TODO transform.execute();
		}
		delete (d);
	}

	return returnvalue;
}

void initializeAndParseASP(pwls d) {
	LParseTranslator* lptrans = new LParseTranslator();
	if (d->getOptions().transformat != OutputFormat::PLAIN) {
		d->setTranslator(lptrans);
	}

	std::istream is(getInputBuffer());
	auto r = new Read<Space>(*d, lptrans);

	r->read(is);
	closeInput();
	delete r;
}

void initializeAndParseOPB(pwls d) {
	OPBTranslator* opbtrans = new OPBTranslator();
	if (d->getOptions().transformat != OutputFormat::PLAIN) {
		d->setTranslator(opbtrans);
	}

	std::istream is(getInputBuffer());
	auto parser = new PBRead<Space>(*d, opbtrans, is);

	parser->parse();
	closeInput();
	delete parser;

	if (d->getOptions().transformat == OutputFormat::PLAIN) {
		delete (opbtrans);
	}
}

void initializeAndParseFODOT(pwls d) {
	yyin = getInputFile();

	yyinit();

	setSpace(d);

	try {
		yyparse();
	} catch (const MinisatID::idpexception& e) {
		if (d->isCertainlyUnsat()) {
			printUnsatFoundDuringParsing(clog, d->getOptions().verbosity);
		} else {
			throw idpexception(getParseError(e, lineNo, charPos, yytext));
		}
	}

	yydestroy();

	closeInput();
}

void parseAndInitializeTheory(pwls d) {
	auto startparsing = cpuTime();

	switch (d->getOptions().format) {
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

	auto endparsing = cpuTime();
	if(d->getOptions().verbosity>1){
		clog <<">>> Parsing time: " <<endparsing-startparsing <<"\n";
	}
}

void doModelGeneration(pwls d) {
	ModelExpandOptions mxoptions;
	mxoptions.printmodels = Models::ALL;
	mxoptions.savemodels = Models::NONE;
	if (d->getOptions().format == InputFormat::OPB && d->isOptimizationProblem()) { // Change default options added before parsing
		mxoptions.printmodels = Models::BEST;
		mxoptions.savemodels = Models::BEST;
	}
	mxoptions.nbmodelstofind = d->getOptions().nbmodels;

	mx = new ModelExpand(d, mxoptions, {});
	mx->execute();
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
