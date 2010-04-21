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

shared_ptr<Solver>			solver;
shared_ptr<ModSolverHier>	modhier;
shared_ptr<IDSolver>		idsolver;
shared_ptr<AggSolver>		aggsolver;

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
	idsolver.reset();
	aggsolver.reset();
	modhier.reset();
	weights.clear();
	lits.clear();
}

//Auxiliary variables, used while parsing.
int lineNo = 1;
int charPos = 1;

/*
 * Prints an error message when a input error has been found and exits the program.
 */
void error(bool during_parsing, const char * msg) {
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
inline Var readLit(int nb){
	Var var = abs(nb)-1;
	if(solver.get()!=NULL){
		while (var >= solver->nVars()) solver->newVar();
		solver->setDecisionVar(var,true); // S.nVars()-1   or   var	
	}
	return var;
}

/**
 * Reads the new literal and adds it to the current list of literals
 */
inline void addLit(int nb){
	Var var = readLit(nb);
	lits.push( (nb > 0) ? Lit(var) : ~Lit(var) );
}

inline void addSet(int modid, int setid, const vec<Lit>& lits, const vector<Weight>& weights){
	if(modhier->getModSolver(modid)==NULL){
		reportf("No modal operator with id %d was defined! ", modid+1);
		error(true, "");
	}
	modhier->getModSolver(modid)->addSet(setid, lits, weights);
}

inline void addQuantSet(bool exists, int modid, int head, const vector<int>& atoms){
	modhier->addModSolver(modid, head, exists, atoms); 
}

inline void addChildren(int parent, const vector<int>& children){
	if(modhier->getModSolver(parent)==NULL){
		reportf("No modal operator with id %d was defined! ", parent+1);
		error(true, "");
	}
	for(vector<int>::const_iterator i=children.begin(); i<children.end(); i++){
		if(modhier->getModSolver(*i)==NULL){
			reportf("No modal operator with id %d was defined! ", *i+1);
			error(true, "");
		}
	}
	modhier->getModSolver(parent)->setChildren(children);
}

inline void addClause(int modid, const vec<Lit>& lits){
	if(modhier->getModSolver(modid)==NULL){
		reportf("No modal operator with id %d was defined! ", modid+1);
		error(true, "");
	}
	modhier->getModSolver(modid)->addClause(lits); 
}

/**
 * Adds an aggregate expression, with given parameters to the solver
 */
inline void addAgg(int head, int setid, int w, AggrType a, bool l, bool d){
	if(head<1){
		error(false, "No negative heads are allowed!\n");
	}
	aggsolver->addAggrExpr(readLit(head), setid, Weight(w), l, a, d); 
}

inline void addAgg(int modid, int head, int setid, int w, AggrType a, bool l, bool d){
	if(modhier->getModSolver(modid)==NULL){
		reportf("No modal operator with id %d was defined! ", modid+1);
		error(true, "");
	}
	if(head<1){
		error(false, "No negative heads are allowed!\n");
	}
	modhier->getModSolver(modid)->addAggrExpr(readLit(head), setid, Weight(w), l, a, d); 
}

inline void initSolvers(){
	solver = shared_ptr<Solver>(new Solver());
	idsolver = shared_ptr<IDSolver>(new IDSolver());
	aggsolver = shared_ptr<AggSolver>(new AggSolver());
        
	solver->setIDSolver(idsolver);
	solver->setAggSolver(aggsolver);
	idsolver->setSolver(solver);
	idsolver->setAggSolver(aggsolver);
	aggsolver->setSolver(solver);
	aggsolver->setIDSolver(idsolver);
}

inline void initModSolver(){
	modhier = shared_ptr<ModSolverHier>(new ModSolverHier());
	modhier->initialize();
}

shared_ptr<Data> getData(){
	if(solver.get()!=NULL){
		return shared_ptr<Data>(new SolverData(solver, idsolver, aggsolver));
	}else if(modhier.get()!=NULL){
		return shared_ptr<Data>(new ModSolverData(modhier));
	}
	assert(false);
	exit(1);
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

init	:	header {initSolvers();} theory
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
		|	mtheory rule
		| 	mtheory msum
		| 	mtheory mmax
		| 	mtheory mmin
		| 	mtheory mcard
		| 	mtheory mprod
		|	mtheory mset
		|	mtheory mwset
		;

rule	:	SEMDEFN NUMBER                  
						{ 	if ($2 < 0) error(true, "Encountered a rule with negative literal as head.");
							addLit($2);
							disj = $1;
						}
			body ZERO  	{ idsolver->addRule(!disj, lits); lits.clear(); }
		;
			
mnmz	:	MNMZDEFN body ZERO				{ solver->addMinimize(lits, false); lits.clear();}
subsetmnmz: SUBSETMINDEFN body ZERO 		{ solver->addMinimize(lits, true); lits.clear();}
summnmz :	SUMMINDEFN NUMBER NUMBER ZERO 	{ solver->addSumMinimize(readLit($2), $3); }

body	:  /* empty */
		|  body NUMBER { addLit($2); }
		;
		
intbody	:  /* empty */
		|  intbody NUMBER { nb.push_back($2); }
		;
		
varbody	:  /* empty */
		|  varbody NUMBER { nb.push_back($2-1); }
		;
         
wbody	:	/* empty */
		|	wbody NUMBER EQ ZERO	{ addLit($2); weights.push_back(Weight(0)); }
		|	wbody NUMBER EQ NUMBER	{ addLit($2); weights.push_back(Weight($4)); }
		;
       
		
//NONMODAL VERSION
		
clause	:  body ZERO	{ solver->addClause(lits); lits.clear(); }
		;
sum		:	SUMDEFN  SEMDEFN SIGNDEFN NUMBER NUMBER NUMBER ZERO	{ readLit($4); addAgg($4, $5, $6, SUM, $3, $2); }
		;
max		:	MAXDEFN  SEMDEFN SIGNDEFN NUMBER NUMBER NUMBER ZERO	{ readLit($4); addAgg($4, $5, $6, MAX, $3, $2); }	
		;
min		:	MINDEFN  SEMDEFN SIGNDEFN NUMBER NUMBER NUMBER ZERO	{ readLit($4); addAgg($4, $5, $6, MIN, $3, $2); }	
		;
card	:	CARDDEFN SEMDEFN SIGNDEFN NUMBER NUMBER NUMBER ZERO	{ readLit($4); addAgg($4, $5, $6, SUM, $3, $2); }
		;
prod	:	PRODDEFN SEMDEFN SIGNDEFN NUMBER NUMBER NUMBER ZERO	{ readLit($4); addAgg($4, $5, $6, PROD, $3, $2); }
		;
sum		:	SUMDEFN  SEMDEFN SIGNDEFN NUMBER NUMBER ZERO ZERO	{ readLit($4); addAgg($4, $5, 0, SUM, $3, $2); }
		;
max		:	MAXDEFN  SEMDEFN SIGNDEFN NUMBER NUMBER ZERO ZERO	{ readLit($4); addAgg($4, $5, 0, MAX, $3, $2); }	
		;
min		:	MINDEFN  SEMDEFN SIGNDEFN NUMBER NUMBER ZERO ZERO	{ readLit($4); addAgg($4, $5, 0, MIN, $3, $2); }	
		;
card	:	CARDDEFN SEMDEFN SIGNDEFN NUMBER NUMBER ZERO ZERO	{ readLit($4); addAgg($4, $5, 0, SUM, $3, $2); }
		;
prod	:	PRODDEFN SEMDEFN SIGNDEFN NUMBER NUMBER ZERO ZERO	{ readLit($4); addAgg($4, $5, 0, PROD, $3, $2); }
		;

set		:	SETDEFN NUMBER { setid = $2;	}
			body ZERO	{ 
							for(int i=0; i<lits.size(); i++){
								weights.push_back(1);
							}
							aggsolver->addSet(setid, lits, weights);
							lits.clear(); weights.clear();
						}
		;

wset	:	WSETDEFN NUMBER { setid = $2;	}
			wbody ZERO	{ 
							aggsolver->addSet(setid, lits, weights);
							lits.clear(); weights.clear();
						}
		;

//MODAL PART: USE INDEXES+1 AS MODAL IDs IN THE THEORY
matomset:	QUANT NUMBER NUMBER varbody ZERO	{ addQuantSet($1-1, readLit($2), $3, nb); nb.clear(); }
		;
modhier :	MODDEFN	NUMBER varbody ZERO { addChildren($2-1, nb); nb.clear();}
		;
mclause	:	NUMBER body ZERO	{ addClause($1-1, lits); lits.clear(); }
		;
msum	:	SUMDEFN  NUMBER SEMDEFN SIGNDEFN NUMBER NUMBER NUMBER ZERO	{ readLit($5); addAgg($2-1, $5, $6, $7, SUM, $4, $3); }
		;
mmax	:	MAXDEFN  NUMBER SEMDEFN SIGNDEFN NUMBER NUMBER NUMBER ZERO	{ readLit($5); addAgg($2-1, $5, $6, $7, MAX, $4, $3); }	
		;
mmin	:	MINDEFN  NUMBER SEMDEFN SIGNDEFN NUMBER NUMBER NUMBER ZERO	{ readLit($5); addAgg($2-1, $5, $6, $7, MIN, $4, $3); }	
		;
mcard	:	CARDDEFN NUMBER SEMDEFN SIGNDEFN NUMBER NUMBER NUMBER ZERO	{ readLit($5); addAgg($2-1, $5, $6, $7, SUM, $4, $3); }
		;
mprod	:	PRODDEFN NUMBER SEMDEFN SIGNDEFN NUMBER NUMBER NUMBER ZERO	{ readLit($5); addAgg($2-1, $5, $6, $7, PROD, $4, $3); }
		;
msum	:	SUMDEFN  NUMBER SEMDEFN SIGNDEFN NUMBER NUMBER ZERO ZERO	{ readLit($5); addAgg($2-1, $5, $6, 0, SUM, $4, $3); }
		;
mmax	:	MAXDEFN  NUMBER SEMDEFN SIGNDEFN NUMBER NUMBER ZERO ZERO	{ readLit($5); addAgg($2-1, $5, $6, 0, MAX, $4, $3); }	
		;
mmin	:	MINDEFN  NUMBER SEMDEFN SIGNDEFN NUMBER NUMBER ZERO ZERO	{ readLit($5); addAgg($2-1, $5, $6, 0, MIN, $4, $3); }	
		;
mcard	:	CARDDEFN NUMBER SEMDEFN SIGNDEFN NUMBER NUMBER ZERO ZERO	{ readLit($5); addAgg($2-1, $5, $6, 0, SUM, $4, $3); }
		;
mprod	:	PRODDEFN NUMBER SEMDEFN SIGNDEFN NUMBER NUMBER ZERO ZERO	{ readLit($5); addAgg($2-1, $5, $6, 0, PROD, $4, $3); }
		;

mset	:	SETDEFN NUMBER NUMBER { setid = $3; modid = $2-1;	}
			body ZERO	{ 
						for(int i=0; i<lits.size(); i++){
								weights.push_back(1);
							}
							addSet(modid, setid, lits, weights);
							lits.clear(); weights.clear();
						}
		;

mwset	:	WSETDEFN NUMBER NUMBER { setid = $3; modid = $2-1;	}
			wbody ZERO	{ 
							addSet(modid, setid, lits, weights);
							lits.clear(); weights.clear();
						}
		;

%%

int yywrap() {
	cerr << "End of file reached before it was expected... bailing out." << endl;
	return 1;
}
