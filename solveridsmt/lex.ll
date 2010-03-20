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

^"c grounder error".* {cerr << "There was a grounding error, so no solving is possible." << endl; exit(-1);}
^"c ".*      {/* disregard comments */}
^"p cnf".*   {/*return PROBLEMLINE;*/ /* disregard actual data */}

^"p ecnf"  	{ ADJ; }
"def" 		{ ADJ; return DEF_PRESENT;}
"aggr" 		{ ADJ; return AGG_PRESENT;}

"WSet"	{ADJ; return WSET_DEFN;}
"Set"	{ADJ; return SET_DEFN;}
"Card"	{ADJ; return CARD_DEFN;}
"Sum"	{ADJ; return SUM_DEFN;}
"Prod"	{ADJ; return PROD_DEFN;}
"Min"	{ADJ; return MIN_DEFN;}
"Max"	{ADJ; return MAX_DEFN;}

"D"		{ADJ; yylval.boolean = true;  return SEM_DEFN;}
"C"		{ADJ; yylval.boolean = false; return SEM_DEFN;}
"L"		{ADJ; yylval.boolean = true;  return SIGN_DEFN;}
"G"		{ADJ; yylval.boolean = false; return SIGN_DEFN;}

"SubsetMnmz"	{ADJ; return SUBSETMIN_DEFN;}
"Mnmz"     		{ADJ; return MNMZ_DEFN;}
"SumMnmz"		{ADJ; return SUMMIN_DEFN;}

" "	   {ADJ; /* disregard whitespaces */}
"\t"	   {ADJ; /*                       */}
"\n"	   {charPos = 1; lineNo++; /*     */}

"="	   {ADJ; return EQ;}

 /* Longest match is returned -> if e.g. "20", NUMBER is returned.
    If "0", then ZERO is returned since it's the first matching rule.
  */
"0"      {ADJ; return ZERO;}
-?[0-9]+ {ADJ; yylval.integer = atoi(yytext); return NUMBER;}

<*>.	{/* Anything else: parse error */
			parseError = true;
			cerr	<< "Line " << lineNo 
					<< ", Column " << charPos 
					<< ": Parse error (unexpected character '"
					<< yytext
					<< "' encountered)." 
					<< endl;
		}
         
