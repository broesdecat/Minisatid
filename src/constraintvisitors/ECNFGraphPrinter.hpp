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

	void visit(const MinisatID::Implication&){
		throw notYetImplemented("Printing ecnfgraph of inner implication.");
	}

	void visit(const Disjunction& lits) {
		this->printList(lits.literals, " -- ", target(), getPrinter());
		if (lits.literals.size() > 1) {
			target() << " -- " << toString(lits.literals[0], getPrinter()) << " ";
		}
		target() << "[color=blue];\n";
	}

	void visit(const Rule& lits) {
		this->printList(lits.body, " -- ", target(), getPrinter());
		if (lits.body.size() > 1) {
			target() << " -- " << toString(lits.body[0], getPrinter()) << " ";
		}
		target() << "[color=green];\n";
	}

	void visit(const WLSet& set) {
		for (unsigned int i = 0; i < set.wl.size(); ++i) {
			if (i > 0) {
				target() << " -- ";
			}
			target() << toString(set.wl[i].getLit(), getPrinter());
		}
		if (set.wl.size() > 1) {
			target() << " -- " << toString(set.wl[0].getLit(), getPrinter()) << " ";
		}
		target() << "[color=green];\n";
	}
};

}

#endif /* ECNFGRAPHPARSINGMONITOR_HPP_ */
