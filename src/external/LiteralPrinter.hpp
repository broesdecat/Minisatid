/*
 * PrintLiteral.hpp
 *
 *  Created on: Mar 30, 2012
 *      Author: broes
 */

#pragma once

#include <string>
#include <sstream>
#include "Lit.hpp"

namespace MinisatID {
class LiteralPrinter {
public:
	virtual ~LiteralPrinter() {
	}
	virtual std::string toString(VarID id) const{
		std::stringstream ss;
		ss <<id.id;
		return ss.str();
	}
	virtual std::string toString(const Lit& lit) const{
		std::stringstream ss;
		ss <<(sign(lit)?"~":"") <<var(lit);
		return ss.str();
	}

	virtual void setString(const Atom&, const std::string&){};

	virtual bool isTseitin(const Atom&) const { return false; }
};
}
