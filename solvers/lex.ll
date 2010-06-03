%{
/* C++ declarations: */
#include <iostream>
#include "parse.tab.hh"
#include "solverfwd.h"

using namespace std;

extern int lineNo;
extern int charPos;
extern bool parseError;

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
"Card"		{ADJ; yylval.integer = CARD; return AGGDEFN;}
"Sum"		{ADJ; yylval.integer = SUM; return AGGDEFN;}
"Prod"		{ADJ; yylval.integer = PROD; return AGGDEFN;}
"Min"		{ADJ; yylval.integer = MIN; return AGGDEFN;}
"Max"		{ADJ; yylval.integer = MAX; return AGGDEFN;}

"Mod"		{ADJ; return MODDEFN;}

"D"			{ADJ; yylval.boolean = true;  return SEMDEFN;}
"C"			{ADJ; yylval.boolean = false; return SEMDEFN;}
"L"			{ADJ; yylval.boolean = true;  return SIGNDEFN;}
"G"			{ADJ; yylval.boolean = false; return SIGNDEFN;}

"e"			{ADJ; yylval.boolean = true; return QUANTe;} //existential quantifier
"a"			{ADJ; yylval.boolean = false; return QUANTe;} //universal quantifier

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
"0"			{ADJ; yylval.integer = 0; return ZERO;}
-?[0-9]+	{ADJ; yylval.integer = atoi(yytext); return NUMBER;}

<*>.		{/* Anything else: parse error */
				parseError = true;
				cerr	<< "Line " << lineNo 
						<< ", Column " << charPos 
						<< ": Parse error (unexpected character '"
						<< yytext
						<< "' encountered)." 
						<< endl;
				throw 333;
			}
