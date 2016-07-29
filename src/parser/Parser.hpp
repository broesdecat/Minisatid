#pragma once

#include <istream>

namespace MinisatID {
template<class TScanner, class TParser, class ... Values>
class Parser {
private:
	TScanner scanner;
	TParser parser;
public:
	Parser(std::istream* input, Values... values)
			: scanner(input), parser(scanner, values...) {
	}

	int parse() {
		return parser.parse();
	}

	const char* getText() const {
		return scanner.YYText();
	}

	int getLineNumber() const {
		return scanner.lineno();
	}
	int getColumnNumber() const {
		return scanner.YYLeng();
	}
};
}
