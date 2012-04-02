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
		throw notYetImplemented("Printing ecnfgraph of inner implication.");
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
		throw notYetImplemented("Printing ecnfgraph of aggregates.");
	}
	void visit(const InnerReifAggregate&) {
		throw notYetImplemented("Printing ecnfgraph of reified aggregate.");
	}
	void visit(const InnerMinimizeOrderedList&) {
		throw notYetImplemented("Printing ecnfgraph of minimize ordered list.");
	}
	void visit(const InnerMinimizeSubset&) {
		throw notYetImplemented("Printing ecnfgraph of minimize subset.");
	}
	void visit(const InnerMinimizeAgg&) {
		throw notYetImplemented("Printing ecnfgraph of minimize aggregate.");
	}
	void visit(const InnerMinimizeVar&) {
		throw notYetImplemented("Printing ecnfgraph of minimize variable.");
	}
	void visit(const InnerSymmetry&) {
		throw notYetImplemented("Printing ecnfgraph of symmetrye.");
	}
	void visit(const InnerForcedChoices&) {
		throw notYetImplemented("Printing ecnfgraph of forced choice.");
	}
	void visit(const InnerIntVarRange&) {
		throw notYetImplemented("Printing ecnfgraph of range int var.");
	}
	void visit(const InnerIntVarEnum&) {
		throw notYetImplemented("Printing ecnfgraph of enum int var.");
	}
	void visit(const InnerCPAllDiff&) {
		throw notYetImplemented("Printing ecnfgraph of alldifferent.");
	}
	void visit(const InnerCPBinaryRel&) {
		throw notYetImplemented("Printing ecnfgraph of cp binary relation op int.");
	}
	void visit(const InnerCPCount&) {
		throw notYetImplemented("Printing ecnfgraph of cp count.");
	}
	void visit(const InnerCPBinaryRelVar&) {
		throw notYetImplemented("Printing ecnfgraph of cp binary relation op var.");
	}
	void visit(const InnerCPSumWeighted&) {
		throw notYetImplemented("Printing ecnfgraph of weighted cp sum.");
	}
};

}

#endif /* ECNFGRAPHPARSINGMONITOR_HPP_ */
