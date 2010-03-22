%{
#include <iostream>
#include <stdio.h>
#include <cstring>
#include <vector>
#include <list>
#include <map>
#include "Solver.h"
#include "IDSolver.h"
#include "AggSolver.h"
#include "Vec.h"
#include <boost/smart_ptr/shared_ptr.hpp>
#include <boost/smart_ptr/weak_ptr.hpp>
#include <boost/smart_ptr/enable_shared_from_this.hpp>
	
using namespace std;
using namespace boost;
using namespace Aggrs;

extern ECNF_mode modes;

extern int yylex(void);
extern char * yytext;

shared_ptr<Solver>		solver;
shared_ptr<IDSolver>	idsolver;
shared_ptr<AggSolver>	aggsolver;

vector<Weight> weights;
vec<Lit> lits;
bool disj;
int setid;

void yyinit(shared_ptr<Solver> s, shared_ptr<IDSolver> ids, shared_ptr<AggSolver> aggs){
	solver = s;
	idsolver = ids;
	aggsolver = aggs;
}

void yydestroy(){
	solver = shared_ptr<Solver>();
	idsolver = shared_ptr<IDSolver>();
	aggsolver = shared_ptr<AggSolver>();
	weights.clear();
	lits.clear();
}

int lineNo = 1;
int charPos = 1;

//! Auxiliary variables, used while parsing.
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
void yyerror(char* msg) {
	error(true, msg);
}

int readLit(int nb){
	int var = abs(nb)-1;
	while (var >= solver->nVars()) solver->newVar();
	solver->setDecisionVar(var,true); // S.nVars()-1   or   var
	return var;
}

void addLit(int nb){
	int var = readLit(nb);
	lits.push( (nb > 0) ? Lit(var) : ~Lit(var) );
}

inline void addAgg(int h, int setid, int w, AggrType a, bool l, bool d){
	if(h<1){
		error(false, "No negative heads are allowed!\n");
	}
	aggsolver->addAggrExpr(abs(h)-1, setid, Weight(w), l, a, d); 
}

%}

%union {
	int integer;
    bool boolean;
}

%token EQ DISJUNCTION CONJUNCTION ZERO 
%token SUBSETMIN_DEFN MNMZ_DEFN SUMMIN_DEFN
%token SET_DEFN WSET_DEFN SUM_DEFN PROD_DEFN MIN_DEFN MAX_DEFN CARD_DEFN 
%token <integer>   NUMBER
%token <boolean> SEM_DEFN SIGN_DEFN
%token DEF_PRESENT AGG_PRESENT

%start init

%%

init	:	header theory
		;

header	: 	/*empty*/
		| 	header DEF_PRESENT	{ modes.def = true;}
		| 	header AGG_PRESENT	{ modes.aggr = true; }
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
		;

clause	:  body ZERO	{ 	solver->addClause(lits); lits.clear(); }
		;

rule	:	SEM_DEFN NUMBER                  
						{ 	if ($2 < 0) error(true, "Encountered a rule with negative literal as head.");
							addLit($2);
							disj = $1;
						}
			body ZERO  	{ idsolver->addRule(!disj, lits); lits.clear(); }
		;
            
sum		:	SUM_DEFN  SEM_DEFN SIGN_DEFN NUMBER NUMBER NUMBER ZERO	{ readLit($4); addAgg($4, $5, $6, SUM, $3, $2); }
		;
max		:	MAX_DEFN  SEM_DEFN SIGN_DEFN NUMBER NUMBER NUMBER ZERO	{ readLit($4); addAgg($4, $5, $6, MAX, $3, $2); }	
		;
min		:	MIN_DEFN  SEM_DEFN SIGN_DEFN NUMBER NUMBER NUMBER ZERO	{ readLit($4); addAgg($4, $5, $6, MIN, $3, $2); }	
		;
card	:	CARD_DEFN SEM_DEFN SIGN_DEFN NUMBER NUMBER NUMBER ZERO	{ readLit($4); addAgg($4, $5, $6, SUM, $3, $2); }
		;
prod	:	PROD_DEFN SEM_DEFN SIGN_DEFN NUMBER NUMBER NUMBER ZERO	{ readLit($4); addAgg($4, $5, $6, PROD, $3, $2); }
		;
sum		:	SUM_DEFN  SEM_DEFN SIGN_DEFN NUMBER NUMBER ZERO ZERO	{ readLit($4); addAgg($4, $5, 0, SUM, $3, $2); }
		;
max		:	MAX_DEFN  SEM_DEFN SIGN_DEFN NUMBER NUMBER ZERO ZERO	{ readLit($4); addAgg($4, $5, 0, MAX, $3, $2); }	
		;
min		:	MIN_DEFN  SEM_DEFN SIGN_DEFN NUMBER NUMBER ZERO ZERO	{ readLit($4); addAgg($4, $5, 0, MIN, $3, $2); }	
		;
card	:	CARD_DEFN SEM_DEFN SIGN_DEFN NUMBER NUMBER ZERO ZERO	{ readLit($4); addAgg($4, $5, 0, SUM, $3, $2); }
		;
prod	:	PROD_DEFN SEM_DEFN SIGN_DEFN NUMBER NUMBER ZERO ZERO	{ readLit($4); addAgg($4, $5, 0, PROD, $3, $2); }
		;

set		:	SET_DEFN NUMBER { setid = $2;	}
			body ZERO	{ 
							for(int i=0; i<lits.size(); i++){
								weights.push_back(1);
							}
							aggsolver->addSet(setid, lits, weights);
							lits.clear(); weights.clear();
						}
		;

wset	:	WSET_DEFN NUMBER { setid = $2;	}
			wbody ZERO	{ 
							aggsolver->addSet(setid, lits, weights);
							lits.clear(); weights.clear();
						}
		;

body     :  /* empty */
         |  body NUMBER { addLit($2); }
         ;
         
wbody	:	/* empty */
		|	wbody NUMBER EQ ZERO	{ addLit($2); weights.push_back(Weight(0)); }
		|	wbody NUMBER EQ NUMBER	{ addLit($2); weights.push_back(Weight($4)); }
		;
		
mnmz	:	MNMZ_DEFN body ZERO		{ solver->addMinimize(lits, false); lits.clear();}
		
//TODO MINIMIZATION
            
%%

int yywrap() {
	cerr << "End of file reached before it was expected... bailing out." << endl;
	return 1;
}
