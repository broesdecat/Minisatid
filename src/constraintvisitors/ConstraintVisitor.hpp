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
#include "theorysolvers/PCSolver.hpp" // TODO use a higher class then pcsolver?

namespace MinisatID{

// TODO name visitor is wrong, is there is no hierarchy which is visited!
class ConstraintVisitor {
private:
	PCSolver* pcsolver; // TODO set!
protected:
	PCSolver* getPCSolver() const { return pcsolver; }

	template<typename S>
	void printList(const litlist& list, const std::string& concat, S& stream, PCSolver* solver){
		bool begin = true;
		for(auto i=list.cbegin(); i<list.cend(); ++i) {
			if(not begin){
				stream <<concat;
			}
			begin = false;
			stream <<print(*i, solver);
		}
	}
public:
	virtual ~ConstraintVisitor(){}

	virtual void notifyStart() = 0;
	virtual void notifyEnd() = 0;

	virtual void visit(const InnerDisjunction&) = 0;
	virtual void visit(const InnerImplication&) = 0;
	virtual void visit(const InnerRule&) = 0;
	virtual void visit(const InnerWLSet&) = 0;
	virtual void visit(const InnerAggregate&) = 0;
	virtual void visit(const InnerReifAggregate&) = 0;
	virtual void visit(const InnerMinimizeOrderedList&) = 0;
	virtual void visit(const InnerMinimizeSubset&) = 0;
	virtual void visit(const InnerMinimizeVar&) = 0;
	virtual void visit(const InnerMinimizeAgg&) = 0;
	virtual void visit(const InnerSymmetry&) = 0;
	virtual void visit(const InnerForcedChoices&) = 0;
	virtual void visit(const InnerIntVarEnum&) = 0;
	virtual void visit(const InnerIntVarRange&) = 0;
	virtual void visit(const InnerCPAllDiff&) = 0;
	virtual void visit(const InnerCPBinaryRel&) = 0;
	virtual void visit(const InnerCPCount&) = 0;
	virtual void visit(const InnerCPBinaryRelVar&) = 0;
	virtual void visit(const InnerCPSumWeighted&) = 0;
};

template<typename Stream>
class ConstraintAdditionMonitor: public ConstraintVisitor{
private:
	Stream& stream;
public:
	ConstraintAdditionMonitor(Stream& stream): stream(stream){}
protected:
	Stream& target() { return stream; }
};
}

#endif /* PARSINGMONITOR_HPP_ */
