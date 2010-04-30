%{
#include <iostream>
#include <stdio.h>
#include <cstring>
#include <vector>
#include <list>
#include <map>
	
#include "solverfwd.h"
#include "SOSolverHier.h"
#include "PCSolver.h"
#include "Vec.h"
	
using namespace Aggrs;

extern ECNF_mode modes;

extern int yylex(void);
extern char * yytext;

bool mod;
shared_ptr<PCSolver>		solver;
shared_ptr<ModSolverData>	modsolver;

vector<Weight> weights;
vector<Var> nb;
vec<Lit> lits;
bool disj;
int setid, modid;
bool unsatfound;

/**
 * Initializes the solvers to add the datastructures
 */
void yyinit(){
	unsatfound = false;
}

/**
 * Removes the solvers, releasing their locks and empties the temporary datastructures
 */
void yydestroy(){
	solver.reset();
	modsolver.reset();
	weights.clear();
	lits.clear();
}

//Auxiliary variables, used while parsing.
int lineNo = 1;
int charPos = 1;

/*
 * Prints an error message when a input error has been found and exits the program.
 */
/*bool error(bool during_parsing, const char * msg) {
	cerr << "Parse error: ";
	if (during_parsing){
		cerr << "Line " << lineNo << ", column " << charPos << ": "; 
	}
	cerr << msg;
	if (during_parsing && strlen(yytext)){
		cerr << " on \"" << yytext << "\"";		
	}
	cerr << endl;
	exit(1);
}*/

// If an unforeseen parse error occurs, it calls this function (e.g. with msg="syntax error")
void yyerror(const char* msg) {
	if(unsatfound){
		return; //this is used to stop the parser when unsat has been found
	}else{
		cerr << "Parse error: ";
		cerr << "Line " << lineNo << ", column " << charPos << ": "; 
		cerr << msg;
		if (strlen(yytext)){
			cerr << " on \"" << yytext << "\"";		
		}
		cerr << endl;
	}	
}


/**
 * CR-CheckResult: checks the result of passing some data to the solvers.
 * The result is false if unsat was already detected.
 */
void CR(bool result){
	if(!result){
		unsatfound = true;
		yyerror("Unsat was found during parsing");
	}		
}

/**
 * Parses the input integer (a literal) to a variable and notifies the solver of its existence
 */
inline Var readVar(int nb){
	Var var = abs(nb)-1;
	if(!mod){
		solver->addVar(var);
	}else{
		modsolver->addVar(var);	
	}
	return var;
}

inline Lit readLit(int nb){
	Var var = readVar(nb);
	return (nb > 0) ? Lit(var) : ~Lit(var);
}

/**
 * Reads the new literal and adds it to the current list of literals
 */
inline void addLit(int nb){
	lits.push( readLit(nb) );
}

void initSolver(){
	solver = shared_ptr<PCSolver>(new PCSolver());
	mod = false;
}

void initModSolver(){
	modsolver = shared_ptr<ModSolverData>(new ModSolverData());
	modsolver->initialize();
	mod = true;
}

shared_ptr<Data> getData(){
	if(solver.get()!=NULL){
		return solver;
	}else{
		return modsolver;
	}
}

%}

//for a reentrant parser, you need to use %pureparser

%union {
	int integer;
    bool boolean;
}

%token EQ DISJUNCTION CONJUNCTION ZERO
%token SUBSETMINDEFN MNMZDEFN SUMMINDEFN
%token SETDEFN WSETDEFN SUMDEFN PRODDEFN MINDEFN MAXDEFN CARDDEFN 
%token <integer> NUMBER
%token <boolean> SEMDEFN SIGNDEFN
%token DEFPRESENT AGGPRESENT MNMZPRESENT MODPRESENT QUANT MODDEFN

%start init

%%

init	:	header {initSolver();} theory
		|	header MODPRESENT {initModSolver();} mtheory
		;

header	: 	/*empty*/
		| 	header DEFPRESENT	{ modes.def = true;}
		| 	header AGGPRESENT	{ modes.aggr = true; }
		| 	header MNMZPRESENT	{ modes.mnmz = true; }
		;

theory	:	/* empty */
		|	theory clause
		|	theory rule
		| 	theory sum
		| 	theory max
		| 	theory min
		| 	theory card
		| 	theory prod
		|	theory set
		|	theory wset
		|	theory mnmz
		|	theory subsetmnmz
		|	theory summnmz
		;
		
mtheory	:	/* empty */
		|	mtheory matomset
		|	mtheory modhier
		|	mtheory mclause
		|	mtheory mrule
		| 	mtheory msum
		| 	mtheory mmax
		| 	mtheory mmin
		| 	mtheory mcard
		| 	mtheory mprod
		|	mtheory mset
		|	mtheory mwset
		;
			
mnmz	:	MNMZDEFN body ZERO				{ CR(solver->addMinimize(lits, false)); lits.clear();}
subsetmnmz: SUBSETMINDEFN body ZERO 		{ CR(solver->addMinimize(lits, true)); lits.clear();}
summnmz :	SUMMINDEFN NUMBER NUMBER ZERO 	{ CR(solver->addSumMinimize(readVar($2), $3)); }

body	:  /* empty */
		|  body NUMBER { addLit($2); }
		;
		
varbody	:  /* empty */
		|  varbody NUMBER { nb.push_back($2-1); }
		;
         
wbody	:	/* empty */
		|	wbody NUMBER EQ ZERO	{ addLit($2); weights.push_back(Weight(0)); }
		|	wbody NUMBER EQ NUMBER	{ addLit($2); weights.push_back(Weight($4)); }
		;
       
		
//NONMODAL VERSION
		
clause	:  body ZERO	{ CR(solver->addClause(lits)); lits.clear(); }
		;
rule	:	SEMDEFN NUMBER                  
						{ 	if ($2 < 0) yyerror("Encountered a rule with negative literal as head.");
							addLit($2);
							disj = $1;
						}
			body ZERO  	{ CR(solver->addRule(!disj, lits)); lits.clear(); }
		;
sum		:	SUMDEFN  SEMDEFN SIGNDEFN NUMBER NUMBER NUMBER ZERO	{ CR(solver->addAggrExpr(readLit($4), $5, Weight($6), $3, SUM, $2)); }
		;
max		:	MAXDEFN  SEMDEFN SIGNDEFN NUMBER NUMBER NUMBER ZERO	{ CR(solver->addAggrExpr(readLit($4), $5, Weight($6), $3, MAX, $2)); }	
		;
min		:	MINDEFN  SEMDEFN SIGNDEFN NUMBER NUMBER NUMBER ZERO	{ CR(solver->addAggrExpr(readLit($4), $5, Weight($6), $3, MIN, $2)); }	
		;
card	:	CARDDEFN SEMDEFN SIGNDEFN NUMBER NUMBER NUMBER ZERO	{ CR(solver->addAggrExpr(readLit($4), $5, Weight($6), $3, SUM, $2)); }
		;
prod	:	PRODDEFN SEMDEFN SIGNDEFN NUMBER NUMBER NUMBER ZERO	{ CR(solver->addAggrExpr(readLit($4), $5, Weight($6), $3, PROD, $2)); }
		;
sum		:	SUMDEFN  SEMDEFN SIGNDEFN NUMBER NUMBER ZERO ZERO	{ CR(solver->addAggrExpr(readLit($4), $5, Weight(0), $3, SUM, $2)); }
		;
max		:	MAXDEFN  SEMDEFN SIGNDEFN NUMBER NUMBER ZERO ZERO	{ CR(solver->addAggrExpr(readLit($4), $5, Weight(0), $3, MAX, $2)); }	
		;
min		:	MINDEFN  SEMDEFN SIGNDEFN NUMBER NUMBER ZERO ZERO	{ CR(solver->addAggrExpr(readLit($4), $5, Weight(0), $3, MIN, $2)); }	
		;
card	:	CARDDEFN SEMDEFN SIGNDEFN NUMBER NUMBER ZERO ZERO	{ CR(solver->addAggrExpr(readLit($4), $5, Weight(0), $3, SUM, $2)); }
		;
prod	:	PRODDEFN SEMDEFN SIGNDEFN NUMBER NUMBER ZERO ZERO	{ CR(solver->addAggrExpr(readLit($4), $5, Weight(0), $3, PROD, $2)); }
		;

set		:	SETDEFN NUMBER { setid = $2;	}
			body ZERO	{ 
							for(int i=0; i<lits.size(); i++){
								weights.push_back(1);
							}
							CR(solver->addSet(setid, lits, weights));
							lits.clear(); weights.clear();
						}
		;

wset	:	WSETDEFN NUMBER { setid = $2;	}
			wbody ZERO	{ 
							CR(solver->addSet(setid, lits, weights));
							lits.clear(); weights.clear();
						}
		;

//MODAL PART: USE INDEXES+1 AS MODAL IDs IN THE THEORY
matomset:	QUANT NUMBER NUMBER varbody ZERO	{ CR(modsolver->addModSolver($2-1, readLit($3), nb)); nb.clear(); }
		;
modhier :	MODDEFN	NUMBER varbody ZERO { CR(modsolver->addChildren($2-1, nb)); nb.clear();}
		;
mclause	:	NUMBER body ZERO	{ CR(modsolver->addClause($1-1, lits)); lits.clear(); }
		;
mrule	:	SEMDEFN NUMBER NUMBER                  
						{ 	if ($3 < 0) yyerror("Encountered a rule with negative literal as head.");
							addLit($3);
							disj = $1;
						}
			body ZERO  	{ CR(modsolver->addRule($2, !disj, lits)); lits.clear(); }
		;
			
/*
 * bool 	addAggrExpr		(int modid, int head, int setid, Weight bound, bool lower, AggrType type, bool defined);
 * SUMDEFN  NUMBER SEMDEFN SIGNDEFN NUMBER NUMBER NUMBER ZERO
 * type		modid 	defined lower    head	setid	bound
 * addAggrExpr($2-1, $5, $6, Weight($7), $4, type, $3)
 */
			
msum	:	SUMDEFN  NUMBER SEMDEFN SIGNDEFN NUMBER NUMBER NUMBER ZERO	{ CR(modsolver->addAggrExpr($2-1, readLit($5), $6, Weight($7), $4, SUM, $3)); }
		;
mmax	:	MAXDEFN  NUMBER SEMDEFN SIGNDEFN NUMBER NUMBER NUMBER ZERO	{ CR(modsolver->addAggrExpr($2-1, readLit($5), $6, Weight($7), $4, MAX, $3)); }	
		;
mmin	:	MINDEFN  NUMBER SEMDEFN SIGNDEFN NUMBER NUMBER NUMBER ZERO	{ CR(modsolver->addAggrExpr($2-1, readLit($5), $6, Weight($7), $4, MIN, $3)); }	
		;
mcard	:	CARDDEFN NUMBER SEMDEFN SIGNDEFN NUMBER NUMBER NUMBER ZERO	{ CR(modsolver->addAggrExpr($2-1, readLit($5), $6, Weight($7), $4, SUM, $3)); }
		;
mprod	:	PRODDEFN NUMBER SEMDEFN SIGNDEFN NUMBER NUMBER NUMBER ZERO	{ CR(modsolver->addAggrExpr($2-1, readLit($5), $6, Weight($7), $4, PROD, $3)); }
		;
msum	:	SUMDEFN  NUMBER SEMDEFN SIGNDEFN NUMBER NUMBER ZERO ZERO	{ CR(modsolver->addAggrExpr($2-1, readLit($5), $6, Weight(0), $4, SUM, $3)); }
		;
mmax	:	MAXDEFN  NUMBER SEMDEFN SIGNDEFN NUMBER NUMBER ZERO ZERO	{ CR(modsolver->addAggrExpr($2-1, readLit($5), $6, Weight(0), $4, MAX, $3)); }	
		;
mmin	:	MINDEFN  NUMBER SEMDEFN SIGNDEFN NUMBER NUMBER ZERO ZERO	{ CR(modsolver->addAggrExpr($2-1, readLit($5), $6, Weight(0), $4, MIN, $3)); }	
		;
mcard	:	CARDDEFN NUMBER SEMDEFN SIGNDEFN NUMBER NUMBER ZERO ZERO	{ CR(modsolver->addAggrExpr($2-1, readLit($5), $6, Weight(0), $4, SUM, $3)); }
		;
mprod	:	PRODDEFN NUMBER SEMDEFN SIGNDEFN NUMBER NUMBER ZERO ZERO	{ CR(modsolver->addAggrExpr($2-1, readLit($5), $6, Weight(0), $4, PROD, $3)); }
		;

mset	:	SETDEFN NUMBER NUMBER { setid = $3; modid = $2-1;	}
			body ZERO	{ 
						for(int i=0; i<lits.size(); i++){
								weights.push_back(1);
							}
							CR(modsolver->addSet(modid, setid, lits, weights));
							lits.clear(); weights.clear();
						}
		;

mwset	:	WSETDEFN NUMBER NUMBER { setid = $3; modid = $2-1;	}
			wbody ZERO	{ 
						CR(modsolver->addSet(modid, setid, lits, weights));
						lits.clear(); weights.clear();
					}
		;

%%

int yywrap() {
	cerr << "End of file reached before it was expected... bailing out." << endl;
	return 1;
}
