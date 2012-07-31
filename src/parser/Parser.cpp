#include "Parser.hpp"

using namespace MinisatID;

Parser::Parser(std::istream* input)
		: scanner(ECNFScanner(input)), parser(ECNFParser(scanner)) {
}

int Parser::parse() {
	return parser.parse();
}

const char* Parser::getText() const{
	return scanner.YYText();
}

int Parser::getLineNumber() const{
	return scanner.lineno();
}
