%{
/* C++ declarations: */
#include <iostream>
#include "parse.tab.hh"
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

^"c grounder error".*	{cerr << "There was a grounding error, so no solving is possible." << endl; exit(-1);}
^"c ".*		{/* disregard comments */}
^"p cnf".*	{/*return PROBLEMLINE;*/ /* disregard actual data */}

^"p ecnf"  	{ADJ; }
"def" 		{ADJ; return DEFPRESENT;}
"aggr" 		{ADJ; return AGGPRESENT;}
"mod" 		{ADJ; return MODPRESENT;}
"mnmz" 		{ADJ; return MNMZPRESENT;}

"WSet"		{ADJ; return WSETDEFN;}
"Set"		{ADJ; return SETDEFN;}
"Card"		{ADJ; return CARDDEFN;}
"Sum"		{ADJ; return SUMDEFN;}
"Prod"		{ADJ; return PRODDEFN;}
"Min"		{ADJ; return MINDEFN;}
"Max"		{ADJ; return MAXDEFN;}

"D"			{ADJ; yylval.boolean = true;  return SEMDEFN;}
"C"			{ADJ; yylval.boolean = false; return SEMDEFN;}
"L"			{ADJ; yylval.boolean = true;  return SIGNDEFN;}
"G"			{ADJ; yylval.boolean = false; return SIGNDEFN;}

"E"			{ADJ; yylval.boolean = true;  return QUANT;}
"A"			{ADJ; yylval.boolean = false; return QUANT;}

"SubsetMnmz"	{ADJ; return SUBSETMINDEFN;}
"Mnmt"     		{ADJ; return MNMZDEFN;}
"SumMnmz"		{ADJ; return SUMMINDEFN;}

" "			{ADJ; /* disregard whitespaces */}
"\t"		{ADJ; /*                       */}
"\n"		{charPos = 1; lineNo++; /*     */}

"="			{ADJ; return EQ;}

 /* Longest match is returned -> if e.g. "20", NUMBER is returned.
    If "0", then ZERO is returned since it's the first matching rule.
  */
"0"			{ADJ; return ZERO;}
-?[0-9]+	{ADJ; yylval.integer = atoi(yytext); return NUMBER;}

<*>.		{/* Anything else: parse error */
				parseError = true;
				cerr	<< "Line " << lineNo 
						<< ", Column " << charPos 
						<< ": Parse error (unexpected character '"
						<< yytext
						<< "' encountered)." 
						<< endl;
			}
