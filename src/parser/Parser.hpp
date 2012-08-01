#pragma once

#include <istream>

namespace MinisatID {
template<class TScanner, class TParser, class Monitor>
class Parser {
private:
	TScanner scanner;
	TParser parser;
public:
	Parser(std::istream* input, Monitor& monitor)
			: scanner(TScanner(input)), parser(TParser(scanner, monitor)) {
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
