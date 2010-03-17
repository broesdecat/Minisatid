%{
/* C++ declarations: */
#include <iostream>
#include "parse.tab.hh"
using namespace std;

extern int lineNo;
extern int charPos;

char* lexcopy(const char* input) {
   char* rslt = (char*)malloc(strlen(input)+1);
   strcpy(rslt, input);
   return rslt;
}

#define ADJ (charPos += yyleng)
%}
                  
/* lex definitions: */
%option noyywrap

%x TRANSLATION_MODUS
%%

^"c grounder error".* {cerr << "There was a grounding error, so no solving is possible." << endl; exit(-1);}
^"c ".*      {/* disregard comments */}
^"p ecnf def".*  {/*return PROBLEMLINE;*/ /* disregard actual data */}
^"p ecnf aggr".*  {/*return PROBLEMLINE;*/ /* disregard actual data */}
^"p cnf".*   {/*return PROBLEMLINE;*/ /* disregard actual data */}

"WSet"   {ADJ; return WSET_DEFN;}
"Set"    {ADJ; return SET_DEFN;}
"Card"   {ADJ; return CARDINIALITY_DEFN;}
"Sum"    {ADJ; return SUM_DEFN;}
"Prod"	{ADJ; return PROD_DEFN;}
"Min"		{ADJ; return MIN_DEFN;}
"Max"		{ADJ; return MAX_DEFN;}
"LB"		{ADJ; return LOWER;}
"GB"		{ADJ; return GREATER;}
"CS"		{ADJ; return COMPSEM;}
"DS"		{ADJ; return DEFSEM;}

"D"	   {ADJ; return DISJUNCTION;}
"C"	   {ADJ; return CONJUNCTION;}

"SubsetMnmz"	{ADJ; return SUBSETMIN;}
"Mnmz"     		{ADJ; return MIN;}
"SumMnmz"		{ADJ; return SUMMIN;}

" "	   {ADJ; /* disregard whitespaces */}
"\t"	   {ADJ; /*                       */}
"\n"	   {charPos = 1; lineNo++; /*     */}

"="	   {ADJ; return EQ;}

 /* Longest match is returned -> if e.g. "20", NUMBER is returned.
    If "0", then ZERO is returned since it's the first matching rule.
  */
"0"      {ADJ; return ZERO;}
-?[0-9]+ {ADJ; yylval.integer = atoi(yytext); return NUMBER;}

<*>.	      {/* Anything else: parse error */
            /*ADJ;*/
            cerr  << "Line " << lineNo 
               << ", Column " << charPos 
               << ": Parse error (unexpected character '"
               << yytext
               << "' encountered)." 
               << endl;
         }
         