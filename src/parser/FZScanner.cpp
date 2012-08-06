#include "FZScanner.hpp"

// NOTE: for some reason, implementing these in the header leads to undefined references.
// NOTE: do NOT combine the scanner implementations, there are problems with bison inclusion guards for location.hh etc.

int FZ::FZScanner::fzlex(FZParser::semantic_type * lval) {
	fzlval = lval;
	return fzlex();
}
