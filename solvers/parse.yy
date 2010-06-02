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
bool unsatfound = false;
bool parseError = false;

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
		cerr << msg;
	}else{
		cerr << "Parse error: ";
		cerr << "Line " << lineNo << ", column " << charPos << ": "; 
		cerr << msg;
		if (strlen(yytext)){
			cerr << " on \"" << yytext << "\"";		
		}
		cerr << endl;
		parseError = true;
	}	
	throw 333; //Dit is lelijk, maar vermijd veel aanpassingen (YYABORT en YYRETURN)
}

AggrType getAggrType(int type){
	return static_cast<AggrType>(type);
}


/**
 * CR-CheckResult: checks the result of passing some data to the solvers.
 * The result is false if unsat was already detected.
 */
void CR(bool result){
	if(!result){
		unsatfound = true;
		yyerror("Unsat was found during parsing.\n");
	}		
}

/**
 * Parses the input integer (a literal) to a variable and notifies the solver of its existence
 */
inline Var readVar(int nb){
	Var var = abs(nb)-1;
	/*if(!mod){
		solver->addVar(var);
	}else{
		modsolver->addVar(modid, var);	
	}*/
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
	solver = shared_ptr<PCSolver>(new PCSolver(modes));
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
%token SETDEFN WSETDEFN  
%token <integer> NUMBER AGGDEFN
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
		| 	theory agg
		|	theory set
		|	theory wset
		|	theory mnmz
		|	theory subsetmnmz
		|	theory summnmz
		;
		
mtheory	:	mhier mrest
		;

mhier	:	/* empty */
		|	mhier matomset
		|	mhier modhier
		;
		
mrest	: 	/* empty */
		|	mrest mclause
		|	mrest mrule
		| 	mrest magg
		|	mrest mset
		|	mrest mwset
		;
			
mnmz	:	MNMZDEFN body ZERO					{ CR(solver->addMinimize(lits, false)); lits.clear();}
subsetmnmz: SUBSETMINDEFN body ZERO 		{ CR(solver->addMinimize(lits, true)); lits.clear();}
summnmz :	SUMMINDEFN NUMBER NUMBER ZERO { CR(solver->addSumMinimize(readVar($2), $3));}

body	:  /* empty */
		|  body NUMBER { addLit($2); }
		;
		
varbody	:  /* empty */
		|  varbody NUMBER	{ 
									if($2<0){yyerror("Rigid atoms cannot have a sign.\n");}
									nb.push_back(readVar($2)); 
								}
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
agg		:	AGGDEFN  SEMDEFN SIGNDEFN NUMBER NUMBER NUMBER ZERO	{ CR(solver->addAggrExpr(readLit($4), $5, Weight($6), $3, getAggrType($1), $2)); }
		;
agg		:	AGGDEFN  SEMDEFN SIGNDEFN NUMBER NUMBER ZERO ZERO	{ CR(solver->addAggrExpr(readLit($4), $5, Weight(0), $3, getAggrType($1), $2)); }
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

//MODAL PART: USES INDEXES+1 AS MODAL IDs IN THE THEORY
	//FIXME: probleem gevonden: de HEAD kan niet correct aan de juiste worden toegevoegd, 
	//want de parent is nog niet gekend! => ALLE MODS MOETEN EERST IN DE THEORIE!!!
	//FIXME 2: je kan nu vars enzo toevoegen terwijl de kinderen van een mod op nog niet gekend
	//zijn, wat dus onvolledige kennis geeft!
modhier :	MODDEFN	NUMBER 	NUMBER 	NUMBER ZERO 
				{ CR(modsolver->addChild($2-1, $3-1, readLit($4))); }
		;
matomset:	QUANT NUMBER { modid = $2-1; }
			varbody ZERO { modsolver->addAtoms(modid, nb); nb.clear(); }
		;
mclause	:	NUMBER {modid = $1-1;} 
			body ZERO { CR(modsolver->addClause(modid, lits)); lits.clear(); }
		;
mrule	:	SEMDEFN NUMBER {disj = $1; modid = $2-1;} NUMBER                  
						{ 	if ($1 < 0) yyerror("Encountered a rule with negative literal as head.");
							addLit($4);
						}
			body ZERO  { CR(modsolver->addRule(modid, !disj, lits)); lits.clear(); }
		;
			
/*
 * bool 	addAggrExpr		(int modid, int head, int setid, Weight bound, bool lower, AggrType type, bool defined);
 * SUMDEFN  NUMBER SEMDEFN SIGNDEFN NUMBER NUMBER NUMBER ZERO
 * type		modid 	defined lower    head	setid	bound
 * addAggrExpr($2-1, $5, $6, Weight($7), $4, type, $3)
 */
			
magg	:	AGGDEFN  NUMBER SEMDEFN SIGNDEFN NUMBER NUMBER NUMBER ZERO	{ CR(modsolver->addAggrExpr($2-1, readLit($5), $6, Weight($7), $4, getAggrType($1), $3)); }
		;
magg	:	AGGDEFN  NUMBER SEMDEFN SIGNDEFN NUMBER NUMBER ZERO ZERO	{ CR(modsolver->addAggrExpr($2-1, readLit($5), $6, Weight(0), $4, getAggrType($1), $3)); }
		;

mset	:	SETDEFN NUMBER NUMBER { modid = $2-1; setid = $3; }
			body ZERO	{ 
						for(int i=0; i<lits.size(); i++){
								weights.push_back(1);
							}
							CR(modsolver->addSet(modid, setid, lits, weights));
							lits.clear(); weights.clear();
						}
		;

mwset	:	WSETDEFN NUMBER NUMBER { modid = $2-1; setid = $3; }
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
