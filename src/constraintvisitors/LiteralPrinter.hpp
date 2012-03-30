/*
 * PrintLiteral.hpp
 *
 *  Created on: Mar 30, 2012
 *      Author: broes
 */

#ifndef PRINTLITERAL_HPP_
#define PRINTLITERAL_HPP_

#include <string>
#include "satsolver/BasicSATUtils.hpp"

namespace MinisatID {
class LiteralPrinter {
public:
	virtual ~LiteralPrinter() {
	}
	virtual std::string printLiteral(const Lit& lit) const = 0;
};
}

#endif /* PRINTLITERAL_HPP_ */
