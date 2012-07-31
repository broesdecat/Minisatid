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
#include <csetjmp>

#include "Run.hpp"

#include "parser/Lparseread.hpp"
#include "parser/PBread.hpp"

#include "external/Translator.hpp"
#include "external/utils/ResourceManager.hpp"
#include "external/Tasks.hpp"
#include "external/OneShotTasks.hpp"
#include "external/utils/TimingUtils.hpp"
#include "external/FlatZincRewriter.hpp"

#include "utils/Print.hpp"

using namespace std;
using namespace MinisatID;

// For template instantiation:
#include "parser/Lparseread.cpp"
#include "parser/PBread.cpp"

typedef ExternalConstraintVisitor* pwls;

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

void doModelGeneration(Space* d);

MXTask* mx = NULL;

int MinisatID::run(const std::string& inputfile, SolverOption modes) {
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

	printMainStart(modes.verbosity);

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
			switch (modes.inference) {
			case Inference::MODELEXPAND:{
				auto space = Space(modes);
				parseAndInitializeTheory(inputfile, &space);
				doModelGeneration(&space);
				break;}
			case Inference::PROPAGATE:{
				auto space = Space(modes);
				parseAndInitializeTheory(inputfile, &space);
				auto t = UnitPropagate(&space, { });
				t.execute();
				t.writeOutEntailedLiterals();
				break;}
			case Inference::PRINTTHEORY:{
				auto tp = TheoryPrinting::ECNF;
				switch (modes.transformat) {
				case OutputFormat::FZ:
					tp = TheoryPrinting::FZ;
					break;
				case OutputFormat::PLAIN:
					tp = TheoryPrinting::HUMAN;
					break;
				case OutputFormat::FODOT:
					if (modes.tocnf) {
						tp = TheoryPrinting::CNF;
					} else {
						tp = TheoryPrinting::ECNF;
					}
					break;
				default:
					throw notYetImplemented("transforming the theory into ASP");
				}
				if(tp==TheoryPrinting::FZ){
					auto resfile = createResMan(modes.outputfile);
					ostream output(resfile->getBuffer());
					FlatZincRewriter<ostream> t(modes, output);
					parseAndInitializeTheory(inputfile, &t);
					t.execute();
				}else{
					auto space = Space(modes);
					parseAndInitializeTheory(inputfile, &space);
					auto t = Transform(&space, tp);
					t.execute();
				}

				break;}
			case Inference::PRINTGRAPH:{
				auto space = Space(modes);
				parseAndInitializeTheory(inputfile, &space);
				auto t = Transform(&space, TheoryPrinting::ECNFGRAPH);
				t.execute();
				break;}
			case Inference::UNSATCORE:{
				auto t = OneShotUnsatCoreExtraction(modes);
				parseAndInitializeTheory(inputfile, &t);
				t.execute();
				break;}
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
	// TODO print statistics?
	if (not cleanexit) {
		exit(returnvalue);
	}
	return returnvalue;
}

void initializeAndParseASP(const std::string& inputfile, pwls d) {
	LParseTranslator* lptrans = new LParseTranslator();
	if (d->getOptions().transformat != OutputFormat::PLAIN) {
		d->setTranslator(lptrans);
	}

	auto input = getInput(inputfile);
	std::istream is(input->getBuffer());
	auto r = Read<ExternalConstraintVisitor>(*d, lptrans);

	r.read(is);
}

void initializeAndParseOPB(const std::string& inputfile, pwls d) {
	OPBTranslator* opbtrans = new OPBTranslator();
	if (d->getOptions().transformat != OutputFormat::PLAIN) {
		d->setTranslator(opbtrans);
	}

	auto input = getInput(inputfile);
	std::istream is(input->getBuffer());
	auto parser = PBRead<ExternalConstraintVisitor>(*d, opbtrans, is);

	parser.parse();

	if (d->getOptions().transformat == OutputFormat::PLAIN) {
		delete (opbtrans);
	}
}

void initializeAndParseFODOT(const std::string& inputfile, pwls d) {
	auto input = getInput(inputfile);
	yyin = input->getFile();

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

	if (d->getOptions().transformat == OutputFormat::PLAIN) {
		d->setTranslator(new PlainTranslator()); // Empty translator
	}
}

void MinisatID::parseAndInitializeTheory(const std::string& inputfile, ExternalConstraintVisitor* d) {
	auto startparsing = cpuTime();

	switch (d->getOptions().format) {
	case InputFormat::ASP:
		initializeAndParseASP(inputfile, d);
		break;
	case InputFormat::OPB:
		initializeAndParseOPB(inputfile, d);
		break;
	case InputFormat::FODOT: {
		initializeAndParseFODOT(inputfile, d);
		break;
	}
	}

	d->notifyFinishParsing();

	auto endparsing = cpuTime();
	if (d->getOptions().verbosity > 1) {
		clog << ">>> Parsing time: " << endparsing - startparsing << "\n";
	}
}

void doModelGeneration(Space* d) {
	ModelExpandOptions mxoptions(0, Models::ALL, Models::NONE);
	if (d->isOptimizationProblem()) { // Change default options added before parsing
		mxoptions.printmodels = Models::BEST;
		mxoptions.savemodels = Models::BEST;
	}
	mxoptions.nbmodelstofind = d->getOptions().nbmodels;

	mx = new ModelExpand(d, mxoptions, { });
	mx->execute();
}

// Debugging - information printing
static void noMoreMem() {
//Tries to reduce the memory of the solver by reducing the number of learned clauses
//This keeps being called until enough memory is free or no more learned clauses can be deleted (causing abort).
	abortcode = SIGABRT;
	clog << ">>> Signal handled: out of memory\n";
	longjmp(main_loop, 1);
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
