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
	using ConstraintVisitor::getPCSolver;
public:
	ECNFGraphPrinter(Stream& stream) :
			ConstraintAdditionMonitor<Stream>(stream) {
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
		// TODO implement
	}

	void visit(const InnerDisjunction& lits) {
		printList(lits.literals, " -- ", target(), getPCSolver());
		if (lits.literals.size() > 1) {
			target() << " -- " << print(lits.literals[0], getPCSolver()) << " ";
		}
		target() << "[color=blue];\n";
	}

	void visit(const InnerRule& lits) {
		printList(lits.body, " -- ", target(), getPCSolver());
		if (lits.body.size() > 1) {
			target() << " -- " << print(lits.body[0], getPCSolver()) << " ";
		}
		target() << "[color=green];\n";
	}

	void visit(const InnerWLSet& set) {
		for (unsigned int i = 0; i < set.wls.size(); ++i) {
			if (i > 0) {
				target() << " -- ";
			}
			target() << print(set.wls[i].getLit(), getPCSolver());
		}
		if (set.wls.size() > 1) {
			target() << " -- " << print(set.wls[0].getLit(), getPCSolver()) << " ";
		}
		target() << "[color=green];\n";
	}

	void visit(const InnerAggregate&) {
		throw idpexception("Not yet implemented."); // TODO
	}
	void visit(const InnerReifAggregate&) {
		throw idpexception("Not yet implemented."); // TODO
	}
	void visit(const InnerMinimizeOrderedList&) {
		throw idpexception("Not yet implemented."); // TODO
	}
	void visit(const InnerMinimizeSubset&) {
		throw idpexception("Not yet implemented."); // TODO
	}
	void visit(const InnerMinimizeAgg&) {
		throw idpexception("Not yet implemented."); // TODO
	}
	void visit(const InnerMinimizeVar&) {
		throw idpexception("Not yet implemented."); // TODO
	}
	void visit(const InnerSymmetry&) {
		throw idpexception("Not yet implemented."); // TODO
	}
	void visit(const InnerForcedChoices&) {
		throw idpexception("Not yet implemented."); // TODO
	}
	void visit(const InnerIntVarRange&) {
		throw idpexception("Not yet implemented."); // TODO
	}
	void visit(const InnerIntVarEnum&) {
		throw idpexception("Not yet implemented."); // TODO
	}
	void visit(const InnerCPAllDiff&) {
		throw idpexception("Not yet implemented."); // TODO
	}
	void visit(const InnerCPBinaryRel&) {
		throw idpexception("Not yet implemented."); // TODO
	}
	void visit(const InnerCPCount&) {
		throw idpexception("Not yet implemented."); // TODO
	}
	void visit(const InnerCPBinaryRelVar&) {
		throw idpexception("Not yet implemented."); // TODO
	}
	void visit(const InnerCPSumWeighted&) {
		throw idpexception("Not yet implemented."); // TODO
	}
};

}

#endif /* ECNFGRAPHPARSINGMONITOR_HPP_ */
