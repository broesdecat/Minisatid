#pragma once

#include <istream>

// Only include FlexLexer.h if it hasn't been already included
#if ! defined(yyFlexLexerOnce)
#include <FlexLexer.h>
#endif

// Override the interface for yylex since we namespaced it
#undef YY_DECL
#define YY_DECL int MinisatID::ECNFScanner::yylex()

// Include Bison for types / tokens
#include "parser.hh"

namespace MinisatID {
class ECNFScanner: public yyFlexLexer {
public:
	ECNFScanner(std::istream* input)
			: yyFlexLexer(input), yylval(NULL) {
	}

	// save the pointer to yylval so we can change it, and invoke scanner
	int yylex(ECNFParser::semantic_type * lval);

private:
	// Scanning function created by Flex; make this private to force usage
	// of the overloaded method so we can get a pointer to Bison's yylval
	int yylex();

	// point to yylval (provided by Bison in overloaded yylex)
	ECNFParser::semantic_type * yylval;
};
}
