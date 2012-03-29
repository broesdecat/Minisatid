/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */

#ifndef AREALECNFPRINTER_HPP_
#define AREALECNFPRINTER_HPP_

#include "ConstraintVisitor.hpp"
#include "utils/Utils.hpp"
#include "utils/Print.hpp"

namespace MinisatID {

template<typename Stream>
class RealECNFPrinter: public ConstraintAdditionMonitor<Stream> {
private:
	using ConstraintAdditionMonitor<Stream>::target;
public:
	RealECNFPrinter(Stream& stream) :
			ConstraintAdditionMonitor<Stream>(stream) {
	}
	virtual ~RealECNFPrinter() {
	}

	void notifyStart(){}
	void notifyEnd(){
		target().flush();
	}

	void visit(const InnerDisjunction& clause) {
		for (int i = 0; i < clause.literals.size(); ++i) {
			target() << clause.literals[i] << " ";
		}
		target() << "0\n";
	}

	void visit(const InnerRule& rule) {
		target() << (rule.conjunctive ? "C" : "D") << " " << rule.head << " ";
		for (int i = 0; i < rule.body.size(); ++i) {
			target() << rule.body[i] << " ";
		}
		target() << "0\n";
	}

	void visit(const InnerWLSet& set) {
		target() << "WLSet " << set.setID << " ";
		throw idpexception("Not yet implemented."); // TODO
		/*for (uint i = 0; i < set.literals.size(); ++i) {
			target() << set.literals[i] << "=" << set.weights[i] << " ";
		}
		target() << "0\n";*/
	}

	void visit(const InnerReifAggregate& agg) {
		target() << "Added aggregate " << agg.head << " " << (agg.sem == AggSem::COMP ? "<=>" : "<-");
		if (agg.sem == AggSem::DEF) {
			target() << "(" << agg.defID << ")";
		}
		target() << " " << agg.type;
		target() << "( set" << agg.setID << " )" << (agg.sign == AggSign::UB ? "=<" : ">=") << agg.bound;
		target() << "\n";
	}

	void visit(const InnerAggregate&) {
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

#endif //AREALECNFPRINTER_HPP_
