%{
#include <iostream>
#include <stdio.h>
#include <cstring>
#include <vector>
#include <list>
#include <map>
	
#include "solverfwd.h"
#include "Solver.h"
#include "IDSolver.h"
#include "ModSolver.h"
#include "AggSolver.h"
#include "Vec.h"
	
using namespace Aggrs;

extern ECNF_mode modes;

extern int yylex(void);
extern char * yytext;

bool mod;
shared_ptr<SolverData>		solver;
shared_ptr<ModSolverData>	modsolver;

vector<Weight> weights;
vector<Var> nb;
vec<Lit> lits;
bool disj;
int setid, modid;

/**
 * Initializes the solvers to add the datastructures
 */
void yyinit(){

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
bool error(bool during_parsing, const char * msg) {
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
}

// If an unforeseen parse error occurs, it calls this function (e.g. with msg="syntax error")
void yyerror(const char* msg) {
	error(true, msg);
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
	solver = shared_ptr<SolverData>(new SolverData());
	mod = false;
}

void initModSolver(){
	modsolver = shared_ptr<ModSolverData>(new ModSolverData());
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
%token <boolean> SEMDEFN SIGNDEFN QUANT MODDEFN
%token DEFPRESENT AGGPRESENT MNMZPRESENT MODPRESENT

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
			
mnmz	:	MNMZDEFN body ZERO				{ solver->addMinimize(lits, false); lits.clear();}
subsetmnmz: SUBSETMINDEFN body ZERO 		{ solver->addMinimize(lits, true); lits.clear();}
summnmz :	SUMMINDEFN NUMBER NUMBER ZERO 	{ solver->addSumMinimize(readVar($2), $3); }

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
		
clause	:  body ZERO	{ solver->addClause(lits)?error(true, ""):true; lits.clear(); }
		;
rule	:	SEMDEFN NUMBER                  
						{ 	if ($2 < 0) error(true, "Encountered a rule with negative literal as head.");
							addLit($2);
							disj = $1;
						}
			body ZERO  	{ solver->addRule(!disj, lits)?error(true, ""):true; lits.clear(); }
		;
sum		:	SUMDEFN  SEMDEFN SIGNDEFN NUMBER NUMBER NUMBER ZERO	{ solver->addAggrExpr(readLit($4), $5, Weight($6), $3, SUM, $2)?error(true, ""):true; }
		;
max		:	MAXDEFN  SEMDEFN SIGNDEFN NUMBER NUMBER NUMBER ZERO	{ solver->addAggrExpr(readLit($4), $5, Weight($6), $3, MAX, $2)?error(true, ""):true; }	
		;
min		:	MINDEFN  SEMDEFN SIGNDEFN NUMBER NUMBER NUMBER ZERO	{ solver->addAggrExpr(readLit($4), $5, Weight($6), $3, MIN, $2)?error(true, ""):true; }	
		;
card	:	CARDDEFN SEMDEFN SIGNDEFN NUMBER NUMBER NUMBER ZERO	{ solver->addAggrExpr(readLit($4), $5, Weight($6), $3, SUM, $2)?error(true, ""):true; }
		;
prod	:	PRODDEFN SEMDEFN SIGNDEFN NUMBER NUMBER NUMBER ZERO	{ solver->addAggrExpr(readLit($4), $5, Weight($6), $3, PROD, $2)?error(true, ""):true; }
		;
sum		:	SUMDEFN  SEMDEFN SIGNDEFN NUMBER NUMBER ZERO ZERO	{ solver->addAggrExpr(readLit($4), $5, Weight(0), $3, SUM, $2)?error(true, ""):true; }
		;
max		:	MAXDEFN  SEMDEFN SIGNDEFN NUMBER NUMBER ZERO ZERO	{ solver->addAggrExpr(readLit($4), $5, Weight(0), $3, MAX, $2)?error(true, ""):true; }	
		;
min		:	MINDEFN  SEMDEFN SIGNDEFN NUMBER NUMBER ZERO ZERO	{ solver->addAggrExpr(readLit($4), $5, Weight(0), $3, MIN, $2)?error(true, ""):true; }	
		;
card	:	CARDDEFN SEMDEFN SIGNDEFN NUMBER NUMBER ZERO ZERO	{ solver->addAggrExpr(readLit($4), $5, Weight(0), $3, SUM, $2)?error(true, ""):true; }
		;
prod	:	PRODDEFN SEMDEFN SIGNDEFN NUMBER NUMBER ZERO ZERO	{ solver->addAggrExpr(readLit($4), $5, Weight(0), $3, PROD, $2)?error(true, ""):true; }
		;

set		:	SETDEFN NUMBER { setid = $2;	}
			body ZERO	{ 
							for(int i=0; i<lits.size(); i++){
								weights.push_back(1);
							}
							solver->addSet(setid, lits, weights)?error(true, ""):true;
							lits.clear(); weights.clear();
						}
		;

wset	:	WSETDEFN NUMBER { setid = $2;	}
			wbody ZERO	{ 
							solver->addSet(setid, lits, weights)?error(true, ""):true;
							lits.clear(); weights.clear();
						}
		;

//MODAL PART: USE INDEXES+1 AS MODAL IDs IN THE THEORY
matomset:	QUANT NUMBER NUMBER varbody ZERO	{ modsolver->addModSolver($2-1, readVar($3), $1, nb)?error(true, ""):true; nb.clear(); }
		;
modhier :	MODDEFN	NUMBER varbody ZERO { modsolver->addChildren($2-1, nb)?error(true, ""):true; nb.clear();}
		;
mclause	:	NUMBER body ZERO	{ modsolver->addClause($1-1, lits)?error(true, ""):true; lits.clear(); }
		;
mrule	:	SEMDEFN NUMBER NUMBER                  
						{ 	if ($3 < 0) error(true, "Encountered a rule with negative literal as head.");
							addLit($3);
							disj = $1;
						}
			body ZERO  	{ modsolver->addRule($2, !disj, lits)?error(true, ""):true; lits.clear(); }
		;
			
/*
 * bool 	addAggrExpr		(int modid, int head, int setid, Weight bound, bool lower, AggrType type, bool defined);
 * SUMDEFN  NUMBER SEMDEFN SIGNDEFN NUMBER NUMBER NUMBER ZERO
 * type		modid 	defined lower    head	setid	bound
 * addAggrExpr($2-1, $5, $6, Weight($7), $4, type, $3)
 */
			
msum	:	SUMDEFN  NUMBER SEMDEFN SIGNDEFN NUMBER NUMBER NUMBER ZERO	{ modsolver->addAggrExpr($2-1, readLit($5), $6, Weight($7), $4, SUM, $3)?error(true, ""):true; }
		;
mmax	:	MAXDEFN  NUMBER SEMDEFN SIGNDEFN NUMBER NUMBER NUMBER ZERO	{ modsolver->addAggrExpr($2-1, readLit($5), $6, Weight($7), $4, MAX, $3)?error(true, ""):true; }	
		;
mmin	:	MINDEFN  NUMBER SEMDEFN SIGNDEFN NUMBER NUMBER NUMBER ZERO	{ modsolver->addAggrExpr($2-1, readLit($5), $6, Weight($7), $4, MIN, $3)?error(true, ""):true; }	
		;
mcard	:	CARDDEFN NUMBER SEMDEFN SIGNDEFN NUMBER NUMBER NUMBER ZERO	{ modsolver->addAggrExpr($2-1, readLit($5), $6, Weight($7), $4, SUM, $3)?error(true, ""):true; }
		;
mprod	:	PRODDEFN NUMBER SEMDEFN SIGNDEFN NUMBER NUMBER NUMBER ZERO	{ modsolver->addAggrExpr($2-1, readLit($5), $6, Weight($7), $4, PROD, $3)?error(true, ""):true; }
		;
msum	:	SUMDEFN  NUMBER SEMDEFN SIGNDEFN NUMBER NUMBER ZERO ZERO	{ modsolver->addAggrExpr($2-1, readLit($5), $6, Weight(0), $4, SUM, $3)?error(true, ""):true; }
		;
mmax	:	MAXDEFN  NUMBER SEMDEFN SIGNDEFN NUMBER NUMBER ZERO ZERO	{ modsolver->addAggrExpr($2-1, readLit($5), $6, Weight(0), $4, MAX, $3)?error(true, ""):true; }	
		;
mmin	:	MINDEFN  NUMBER SEMDEFN SIGNDEFN NUMBER NUMBER ZERO ZERO	{ modsolver->addAggrExpr($2-1, readLit($5), $6, Weight(0), $4, MIN, $3)?error(true, ""):true; }	
		;
mcard	:	CARDDEFN NUMBER SEMDEFN SIGNDEFN NUMBER NUMBER ZERO ZERO	{ modsolver->addAggrExpr($2-1, readLit($5), $6, Weight(0), $4, SUM, $3)?error(true, ""):true; }
		;
mprod	:	PRODDEFN NUMBER SEMDEFN SIGNDEFN NUMBER NUMBER ZERO ZERO	{ modsolver->addAggrExpr($2-1, readLit($5), $6, Weight(0), $4, PROD, $3)?error(true, ""):true; }
		;

mset	:	SETDEFN NUMBER NUMBER { setid = $3; modid = $2-1;	}
			body ZERO	{ 
						for(int i=0; i<lits.size(); i++){
								weights.push_back(1);
							}
							modsolver->addSet(modid, setid, lits, weights)?error(true, ""):true;
							lits.clear(); weights.clear();
						}
		;

mwset	:	WSETDEFN NUMBER NUMBER { setid = $3; modid = $2-1;	}
			wbody ZERO	{ 
						modsolver->addSet(modid, setid, lits, weights)?error(true, ""):true;
						lits.clear(); weights.clear();
					}
		;

%%

int yywrap() {
	cerr << "End of file reached before it was expected... bailing out." << endl;
	return 1;
}
