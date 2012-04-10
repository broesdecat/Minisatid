/*
 * PrintLiteral.hpp
 *
 *  Created on: Mar 30, 2012
 *      Author: broes
 */

#ifndef PRINTLITERAL_HPP_
#define PRINTLITERAL_HPP_

#include <string>
#include <sstream>
#include "external/Lit.hpp"

namespace MinisatID {
class LiteralPrinter {
public:
	virtual ~LiteralPrinter() {
	}
	virtual std::string toString(const Lit& lit) const{
		std::stringstream ss;
		ss <<(sign(lit)?"-":"") <<var(lit);
		return ss.str();
	}
};
}

#endif /* PRINTLITERAL_HPP_ */
