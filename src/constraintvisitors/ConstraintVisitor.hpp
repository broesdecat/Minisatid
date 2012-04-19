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

namespace MinisatID{

class LiteralPrinter;

class ConstraintVisitor {
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
	ConstraintVisitor(LiteralPrinter* solver): solver(solver){}
	virtual ~ConstraintVisitor(){}

	virtual void notifyStart() = 0;
	virtual void notifyEnd() = 0;

	// TODO add visitor name
	virtual void visit(const Disjunction&){
		throw idpexception("Handling lazygroundLits is not relevant for the current visitor.");
	}
	virtual void visit(const Implication&){
		throw idpexception("Handling lazygroundLits is not relevant for the current visitor.");
	}
	virtual void visit(const Rule&){
		throw idpexception("Handling lazygroundLits is not relevant for the current visitor.");
	}
	virtual void visit(const WLSet&){
		throw idpexception("Handling lazygroundLits is not relevant for the current visitor.");
	}
	virtual void visit(const Aggregate&){
		throw idpexception("Handling lazygroundLits is not relevant for the current visitor.");
	}
	virtual void visit(const MinimizeOrderedList&){
		throw idpexception("Handling lazygroundLits is not relevant for the current visitor.");
	}
	virtual void visit(const MinimizeSubset&){
		throw idpexception("Handling lazygroundLits is not relevant for the current visitor.");
	}
	virtual void visit(const MinimizeVar&){
		throw idpexception("Handling lazygroundLits is not relevant for the current visitor.");
	}
	virtual void visit(const MinimizeAgg&){
		throw idpexception("Handling lazygroundLits is not relevant for the current visitor.");
	}
	virtual void visit(const Symmetry&){
		throw idpexception("Handling lazygroundLits is not relevant for the current visitor.");
	}
	virtual void visit(const IntVarEnum&){
		throw idpexception("Handling lazygroundLits is not relevant for the current visitor.");
	}
	virtual void visit(const IntVarRange&){
		throw idpexception("Handling lazygroundLits is not relevant for the current visitor.");
	}
	virtual void visit(const CPAllDiff&){
		throw idpexception("Handling lazygroundLits is not relevant for the current visitor.");
	}
	virtual void visit(const CPBinaryRel&){
		throw idpexception("Handling lazygroundLits is not relevant for the current visitor.");
	}
	virtual void visit(const CPCount&){
		throw idpexception("Handling lazygroundLits is not relevant for the current visitor.");
	}
	virtual void visit(const CPBinaryRelVar&){
		throw idpexception("Handling lazygroundLits is not relevant for the current visitor.");
	}
	virtual void visit(const CPSumWeighted&){
		throw idpexception("Handling lazygroundLits is not relevant for the current visitor.");
	}
	virtual void visit(const CPElement&){
		throw idpexception("Handling lazygroundLits is not relevant for the current visitor.");
	}
	virtual void visit(const LazyGroundLit&){
		throw idpexception("Handling lazygroundLits is not relevant for the current visitor.");
	}
};

template<typename Stream>
class ConstraintAdditionMonitor: public ConstraintVisitor{
private:
	Stream& stream;
public:
	ConstraintAdditionMonitor(LiteralPrinter* solver, Stream& stream): ConstraintVisitor(solver), stream(stream){}
protected:
	Stream& target() { return stream; }
};
}

#endif /* PARSINGMONITOR_HPP_ */
