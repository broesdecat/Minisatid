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

// TODO print the translation too!
template<typename Stream>
class RealECNFPrinter: public ConstraintAdditionMonitor<Stream> {
private:
	using ConstraintAdditionMonitor<Stream>::target;
	// NOTE: printing the remapped literals here!
public:
	RealECNFPrinter(LiteralPrinter* solver, Stream& stream) :
		ConstraintAdditionMonitor<Stream>(solver, stream) {
}
	virtual ~RealECNFPrinter() {
	}

	void notifyStart(){}
	void notifyEnd(){
		target().flush();
	}

	std::string toString(const Lit& lit){
		std::stringstream ss;
		ss <<(sign(lit)?"-":"") <<(var(lit)+1);
		return ss.str();
	}

	void visit(const Disjunction& clause) {
		for (int i = 0; i < clause.literals.size(); ++i) {
			target() <<toString(clause.literals[i]) << " ";
		}
		target() << "0\n";
	}

	void visit(const Rule& rule) {
		target() << (rule.conjunctive ? "C" : "D") << " " << toString(mkPosLit(rule.head)) << " ";
		for (int i = 0; i < rule.body.size(); ++i) {
			target() << toString(rule.body[i]) << " ";
		}
		target() << "0\n";
	}

	void visit(const WLSet& set) {
		target() << "WLSet " << set.setID << " ";
		for (uint i = 0; i < set.wl.size(); ++i) {
			target() << toString(set.wl[i].getLit()) << "=" << set.wl[i].getWeight() << " ";
		}
		target() << "0\n";
	}

	void visit(const Aggregate& agg) {
		target() << "Added aggregate " <<toString(mkPosLit(agg.head)) << " " << (agg.sem == AggSem::COMP ? "<=>" : "<-");
		if (agg.sem == AggSem::DEF) {
			target() << "(" << agg.defID << ")";
		}
		target() << " " << agg.type;
		target() << "( set" << agg.setID << " )" << (agg.sign == AggSign::UB ? "=<" : ">=") << agg.bound;
		target() << "\n";
	}

	void visit(const Implication&) {
		throw idpexception("Not yet implemented."); // TODO
	}
	void visit(const MinimizeOrderedList&) {
		throw idpexception("Not yet implemented."); // TODO
	}
	void visit(const MinimizeSubset&) {
		throw idpexception("Not yet implemented."); // TODO
	}
	void visit(const MinimizeAgg&) {
		throw idpexception("Not yet implemented."); // TODO
	}
	void visit(const MinimizeVar&) {
		throw idpexception("Not yet implemented."); // TODO
	}
	void visit(const Symmetry&) {
		throw idpexception("Not yet implemented."); // TODO
	}
	void visit(const IntVarRange&) {
		throw idpexception("Not yet implemented."); // TODO
	}
	void visit(const IntVarEnum&) {
		throw idpexception("Not yet implemented."); // TODO
	}
	void visit(const CPAllDiff&) {
		throw idpexception("Not yet implemented."); // TODO
	}
	void visit(const CPBinaryRel&) {
		throw idpexception("Not yet implemented."); // TODO
	}
	void visit(const CPCount&) {
		throw idpexception("Not yet implemented."); // TODO
	}
	void visit(const CPBinaryRelVar&) {
		throw idpexception("Not yet implemented."); // TODO
	}
	void visit(const CPSumWeighted&) {
		throw idpexception("Not yet implemented."); // TODO
	}
};

}

#endif //AREALECNFPRINTER_HPP_
