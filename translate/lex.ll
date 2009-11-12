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

" "	   {ADJ; /* disregard whitespaces */}
"\t"	   {ADJ; /*                       */}
"\n"	   {charPos = 1; lineNo++; /*     */}

"0"      {ADJ; return ZERO;}
-?[0-9]+ {ADJ; yylval.integer = atoi(yytext); return NUMBER;}

^"translation"\n      {charPos = 1; lineNo++; BEGIN(TRANSLATION_MODUS);}

<TRANSLATION_MODUS>" "	   {ADJ; /* disregard whitespaces */}
<TRANSLATION_MODUS>"\t"	   {ADJ; /*                       */}

<TRANSLATION_MODUS>"\n"    {charPos = 1; lineNo++; return NEWLINE;}

<TRANSLATION_MODUS>^"type" {ADJ; return TYPE;}
<TRANSLATION_MODUS>^"show" {ADJ; return SHOW;}
<TRANSLATION_MODUS>"pred"  {ADJ; return PRED;}
<TRANSLATION_MODUS>"func"  {ADJ; return FUNC;}
<TRANSLATION_MODUS>^"true" {ADJ; return ISTRUE;}
<TRANSLATION_MODUS>^"arbitrary" {ADJ; return ARBITRARY;}

<TRANSLATION_MODUS>-?[0-9]+ {ADJ; yylval.integer = atoi(yytext); return NUMBER;}
<TRANSLATION_MODUS>[a-zA-Z_][a-zA-Z0-9_]* {ADJ; yylval.character = lexcopy(yytext); return IDENTIFIER;}

<TRANSLATION_MODUS>":"     {ADJ; return COLON;}
<TRANSLATION_MODUS>"/"     {ADJ; return SLASH;}

<*>.	      {/* Anything else: parse error */
            /*ADJ;*/
            cerr  << "Line " << lineNo 
               << ", Column " << charPos 
               << ": Parse error (unexpected character '"
               << yytext
               << "' encountered)." 
               << endl;
         }
