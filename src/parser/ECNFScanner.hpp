#pragma once

#include <istream>

// Only include FlexLexer.h if it hasn't been already included
#if ! defined(yyFlexLexerOnce)
#undef yyFlexLexer
#define yyFlexLexer ecnfFlexLexer
#include <FlexLexer.h>
#endif

// Override the interface for yylex since we namespaced it
#undef YY_DECL
#define YY_DECL int MinisatID::ECNFScanner::ecnflex()

// Include Bison for types / tokens
#include "ecnfparser/ecnfparser.hh"

namespace MinisatID {
class ECNFScanner: public ecnfFlexLexer {
public:
	ECNFScanner(std::istream* input)
			: ecnfFlexLexer(input), ecnflval(NULL), ecnfloc(NULL) {
	}

	// save the pointer to yylval so we can change it, and invoke scanner
	int ecnflex(ECNFParser::semantic_type * lval, ECNFParser::location_type * loc);

private:
	// Scanning function created by Flex; make this private to force usage
	// of the overloaded method so we can get a pointer to Bison's yylval
	int ecnflex();

	// point to yylval (provided by Bison in overloaded yylex)
	ECNFParser::semantic_type * ecnflval;
	ECNFParser::location_type * ecnfloc;
};
}
