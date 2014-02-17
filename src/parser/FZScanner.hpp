#pragma once

#include <istream>

// Only include FlexLexer.h if it hasn't been already included
#if ! defined(yyFlexLexerOnce)
#undef yyFlexLexer
#define yyFlexLexer fzFlexLexer
#include <FlexLexer.h>
#endif

// Override the interface for yylex since we namespaced it
#undef YY_DECL
#define YY_DECL int FZ::FZScanner::fzlex()

// Include Bison for types / tokens
#include "fzparser/fzparser.hh"

namespace FZ {
class FZScanner: public fzFlexLexer {
public:
	FZScanner(std::istream* input)
			: fzFlexLexer(input), fzlval(NULL), fzloc(NULL) {
	}

	// save the pointer to yylval so we can change it, and invoke scanner
	int fzlex(FZ::FZParser::semantic_type * lval, FZ::FZParser::location_type * loc);

private:
	// Scanning function created by Flex; make this private to force usage
	// of the overloaded method so we can get a pointer to Bison's yylval
	int fzlex();

	// point to yylval (provided by Bison in overloaded yylex)
	FZ::FZParser::semantic_type * fzlval;
	FZ::FZParser::location_type * fzloc;
};
}
