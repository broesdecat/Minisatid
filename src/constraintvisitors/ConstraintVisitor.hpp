/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mari�n, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef PARSINGMONITOR_HPP_
#define PARSINGMONITOR_HPP_

#include <iostream>
#include "utils/Print.hpp"
#include "utils/Utils.hpp"
#include "external/LiteralPrinter.hpp"
#include "external/ConstraintAdditionInterface.hpp"

namespace MinisatID{

class LiteralPrinter;

class ConstraintPrinter: public ConstraintVisitor {
private:
	LiteralPrinter* solver; // NOTE: does not have ownership
protected:
	// NOTE: does not pass ownership
	LiteralPrinter* getPrinter() const { return solver; }

	template<typename S>
	void printList(const litlist& list, const std::string& concat, S& stream, LiteralPrinter* solver){
		bool begin = true;
		for(auto i=list.cbegin(); i<list.cend(); ++i) {
			if(not begin){
				stream <<concat;
			}
			begin = false;
			stream <<toString(*i, solver);
		}
	}

public:
	ConstraintPrinter(LiteralPrinter* solver, const std::string& name): ConstraintVisitor(name), solver(solver){}

	virtual void notifyStart() = 0;
	virtual void notifyEnd() = 0;
};

template<typename Stream>
class ConstraintStreamPrinter : public ConstraintPrinter{
private:
	Stream& stream;
public:
	ConstraintStreamPrinter(LiteralPrinter* solver, Stream& stream, const std::string& name): ConstraintPrinter(solver, name), stream(stream){}
protected:
	Stream& target() { return stream; }
};
}

#endif /* PARSINGMONITOR_HPP_ */
