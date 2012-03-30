/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef ECNFGRAPHPARSINGMONITOR_HPP_
#define ECNFGRAPHPARSINGMONITOR_HPP_

#include "ConstraintVisitor.hpp"
#include "utils/Utils.hpp"

namespace MinisatID {

template<typename Stream>
class ECNFGraphPrinter: public ConstraintAdditionMonitor<Stream> {
private:
	using ConstraintAdditionMonitor<Stream>::target;
	using ConstraintVisitor::getPrinter;
public:
	ECNFGraphPrinter(LiteralPrinter* solver, Stream& stream) :
			ConstraintAdditionMonitor<Stream>(solver, stream) {
	}
	virtual ~ECNFGraphPrinter() {
	}

	virtual void notifyStart() {
		target() << "graph ecnftheory {\n";
	}
	virtual void notifyEnd() {
		target() << "}\n";
		target().flush();
	}

	void visit(const MinisatID::InnerImplication&){
		throw notYetImplemented();
	}

	void visit(const InnerDisjunction& lits) {
		printList(lits.literals, " -- ", target(), getPrinter());
		if (lits.literals.size() > 1) {
			target() << " -- " << print(lits.literals[0], getPrinter()) << " ";
		}
		target() << "[color=blue];\n";
	}

	void visit(const InnerRule& lits) {
		printList(lits.body, " -- ", target(), getPrinter());
		if (lits.body.size() > 1) {
			target() << " -- " << print(lits.body[0], getPrinter()) << " ";
		}
		target() << "[color=green];\n";
	}

	void visit(const InnerWLSet& set) {
		for (unsigned int i = 0; i < set.wls.size(); ++i) {
			if (i > 0) {
				target() << " -- ";
			}
			target() << print(set.wls[i].getLit(), getPrinter());
		}
		if (set.wls.size() > 1) {
			target() << " -- " << print(set.wls[0].getLit(), getPrinter()) << " ";
		}
		target() << "[color=green];\n";
	}

	void visit(const InnerAggregate&) {
		throw notYetImplemented();
	}
	void visit(const InnerReifAggregate&) {
		throw notYetImplemented();
	}
	void visit(const InnerMinimizeOrderedList&) {
		throw notYetImplemented();
	}
	void visit(const InnerMinimizeSubset&) {
		throw notYetImplemented();
	}
	void visit(const InnerMinimizeAgg&) {
		throw notYetImplemented();
	}
	void visit(const InnerMinimizeVar&) {
		throw notYetImplemented();
	}
	void visit(const InnerSymmetry&) {
		throw notYetImplemented();
	}
	void visit(const InnerForcedChoices&) {
		throw notYetImplemented();
	}
	void visit(const InnerIntVarRange&) {
		throw notYetImplemented();
	}
	void visit(const InnerIntVarEnum&) {
		throw notYetImplemented();
	}
	void visit(const InnerCPAllDiff&) {
		throw notYetImplemented();
	}
	void visit(const InnerCPBinaryRel&) {
		throw notYetImplemented();
	}
	void visit(const InnerCPCount&) {
		throw notYetImplemented();
	}
	void visit(const InnerCPBinaryRelVar&) {
		throw notYetImplemented();
	}
	void visit(const InnerCPSumWeighted&) {
		throw notYetImplemented();
	}
};

}

#endif /* ECNFGRAPHPARSINGMONITOR_HPP_ */
