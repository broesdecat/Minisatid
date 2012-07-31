#include "ECNFScanner.hpp"

using namespace MinisatID;

int ECNFScanner::yylex(ECNFParser::semantic_type * lval) {
	yylval = lval;
	return yylex();
}
