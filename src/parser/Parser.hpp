#pragma once

#include <istream>
#include "parser/ECNFScanner.hpp"

namespace MinisatID {
class Parser {
private:
	MinisatID::ECNFScanner scanner;
	MinisatID::ECNFParser parser;
public:
	Parser(std::istream* input);

	const char* getText() const;
	int getLineNumber() const;

	int parse();
};
}
