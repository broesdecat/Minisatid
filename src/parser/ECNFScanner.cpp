#include "ECNFScanner.hpp"

// NOTE: for some reason, implementing these in the header leads to undefined references.
// NOTE: do NOT combine the scanner implementations, there are problems with bison inclusion guards for location.hh etc.

int MinisatID::ECNFScanner::ecnflex(ECNFParser::semantic_type * lval, ECNFParser::location_type * loc) {
	ecnflval = lval;
	ecnfloc = loc;
	return ecnflex();
}
