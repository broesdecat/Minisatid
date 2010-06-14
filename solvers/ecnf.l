%{
/* C++ declarations: */
#include <iostream>
#include "ecnf.y.hpp"
#include "solverfwd.hpp"

using namespace std;

extern int lineNo;
extern int charPos;

#define ADJ (charPos += yyleng)
%}

/* lex definitions: */
%option noyywrap

%x TRANSLATION_MODUS
%%

^"c grounder error".*	{cerr << "There was a grounding error, so no solving is possible." << endl; 
						 throw idpexception();}
^"c ".*		{/* disregard comments */}

^"p "		{ADJ; }
"cnf"		{ADJ; return CNF;}
"ecnf"		{ADJ; return ECNF;}
"def" 		{ADJ; return DEFPRESENT;}
"aggr" 		{ADJ; return AGGPRESENT;}
"mod" 		{ADJ; return MODPRESENT;}
"mnmz" 		{ADJ; return MNMZPRESENT;}

"WSet"		{ADJ; return WSETDEFN;}
"Set"		{ADJ; return SETDEFN;}
"Card"		{ADJ; ecnflval.integer = CARD; return AGGDEFN;}
"Sum"		{ADJ; ecnflval.integer = SUM; return AGGDEFN;}
"Prod"		{ADJ; ecnflval.integer = PROD; return AGGDEFN;}
"Min"		{ADJ; ecnflval.integer = MIN; return AGGDEFN;}
"Max"		{ADJ; ecnflval.integer = MAX; return AGGDEFN;}

"Mod"		{ADJ; return MODDEFN;}

"D"			{ADJ; ecnflval.boolean = true;  return SEMDEFN;}
"C"			{ADJ; ecnflval.boolean = false; return SEMDEFN;}
"L"			{ADJ; ecnflval.boolean = true;  return SIGNDEFN;}
"G"			{ADJ; ecnflval.boolean = false; return SIGNDEFN;}

"e"			{ADJ; ecnflval.boolean = true; return QUANTe;} //existential quantifier
"a"			{ADJ; ecnflval.boolean = false; return QUANTe;} //universal quantifier

"Mnmz"		{ADJ; return SUBSETMINDEFN;}
"Mnmt"     	{ADJ; return MNMZDEFN;}
"SumMnmz"	{ADJ; return SUMMINDEFN;}

" "			{ADJ; /* disregard whitespaces */}
"\t"		{ADJ; /*                       */}
"\n"		{charPos = 1; lineNo++; /*     */}

"="			{ADJ; return EQ;}

 /* Longest match is returned -> if e.g. "20", NUMBER is returned.
    If "0", then ZERO is returned since it's the first matching rule.
  */
"0"			{ADJ; ecnflval.integer = 0; return ZERO;}
-?[0-9]+	{ADJ; ecnflval.integer = atoi(yytext); return NUMBER;}

<*>.		{/* Anything else: parse error */
				cerr	<< "Line " << lineNo 
						<< ", Column " << charPos 
						<< ": Parse error (unexpected character '"
						<< yytext
						<< "' encountered)." 
						<< endl;
				throw idpexception();
			}
