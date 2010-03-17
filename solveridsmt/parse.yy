%{
#include <iostream>
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

/*! \file parse.tab.cc
 */

#define min(x,y) ( (x<y) ? x : y)

char* copy(const char* input) {
   char* rslt = (char*)malloc(strlen(input)+1);
   strcpy(rslt, input);
   return rslt;
}

extern int yylex(void);
extern char * yytext;

shared_ptr<Solver> 		solver;
shared_ptr<IDSolver> 	idsolver;
shared_ptr<AggSolver> 	aggsolver;

void yyinit(shared_ptr<Solver> s, shared_ptr<IDSolver> ids, shared_ptr<AggSolver> aggs){
	solver = s;
	idsolver = ids;
	aggsolver = aggs;
}

void yydestroy(){
	solver = shared_ptr<Solver>();
	idsolver = shared_ptr<IDSolver>();
	aggsolver = shared_ptr<AggSolver>();
}

int lineNo = 1;
int charPos = 1;

//! Auxiliary variables, used while parsing.
void error(bool during_parsing, char *msg) {
   cerr << "Parse error: ";
   if (during_parsing)
      cerr << "Line " << lineNo << ", column " << charPos << ": ";
   cerr << msg;
   if (during_parsing && strlen(yytext))
      cerr << " on \"" << yytext << "\"";
   cerr << endl;
   exit(-1);
}

// If an unforeseen parse error occurs, it calls this function (e.g. with msg="syntax error")
void yyerror(char* msg) {
   error(true, msg);
}

vector<int> numbers;

void readclause(vec<Lit>& lits){
	int var;
	for(vector<int>::iterator i=numbers.begin(); i<numbers.end(); i++){
		if ((*i) == 0) break;
		var = abs((*i))-1;
		while (var >= solver->nVars()) solver->newVar();
		solver->setDecisionVar(var,true); // S.nVars()-1   or   var
		lits.push( ((*i) > 0) ? Lit(var) : ~Lit(var) );
	}
}

/*! Finished parsing a clause.
 */
void addclause() {
	cout << "Clause";
	for(vector<int>::iterator i=numbers.begin(); i<numbers.end(); i++){
		cout << *i <<" ";
	}
	cout <<endl;
	
	vec<Lit> lits;
	readclause(lits);
	solver->addClause(lits);
	numbers.clear();
}

/*! Finished parsing a rule.
 */
void adddisjrule(int hd) {
	cout << "Disj rule, head " <<hd <<", body ";
	for(vector<int>::iterator i=numbers.begin(); i<numbers.end(); i++){
		cout << *i <<" ";
	}
	cout <<endl;
	
	vec<Lit> lits;
	readclause(lits);
	idsolver->addRule(false, lits);
	numbers.clear();
}

void addconjrule(int hd){
	cout << "Conj rule, head " <<hd <<", body ";
	for(vector<int>::iterator i=numbers.begin(); i<numbers.end(); i++){
		cout << *i <<" ";
	}
	cout <<endl;
	
	vec<Lit> lits;
	readclause(lits);
	idsolver->addRule(true, lits);
	numbers.clear();
}

%}

%union {
	int integer;
   char* character;
}

%token EQ DISJUNCTION CONJUNCTION ZERO 
%token SUBSETMIN MIN SUMMIN LOWER GREATER COMPSEM DEFSEM
%token SET_DEFN CARDINIALITY_DEFN SUM_DEFN PROD_DEFN MIN_DEFN MAX_DEFN WSET_DEFN
%token <integer>   NUMBER

%start init

%%

init     :  ground
         ;

ground   :
            theory
         ;

theory   :  /* empty */
         |  theory clause
         |  theory rule
         ;

clause   :  body ZERO                            { addclause(); }
         ;

rule     :  DISJUNCTION NUMBER                   { if ($2 < 0) error(true, "Encountered a rule with negative literal as head.");
                                                 }
            body ZERO                            { adddisjrule($2); }
         |  CONJUNCTION NUMBER                   { if ($2 < 0) error(true, "Encountered a rule with negative literal as head.");
                                                 }
            body ZERO                            { addconjrule($2); }
         ;

body     :  /* empty */
         |  body NUMBER                          { numbers.push_back($2); }
         ;
            
%%

/* yywrap: Called when EOF is reached on current input.
 * Have it return 1 if processing is finished, or
 * do something to fix the EOF condition (like open
 * another file and point to it) and return 0 to indicate
 * more input is available.
 */
//extern int yylex();

int yywrap() {
   cerr << "End of file reached before it was expected... bailing out." << endl;
	return 1;
}