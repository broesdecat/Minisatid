/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */

#ifndef REALCNFPRINTER_HPP_
#define REALCNFPRINTER_HPP_

#include "ConstraintVisitor.hpp"
#include "utils/Utils.hpp"
#include "utils/Print.hpp"

namespace MinisatID {

template<typename Stream>
class RealCNFPrinter: public ConstraintAdditionMonitor<Stream> {
private:
	std::stringstream ss;
	int nbconstraints, maxvar;
	using ConstraintAdditionMonitor<Stream>::target;
	// NOTE: printing the remapped literals here!
public:
	RealCNFPrinter(LiteralPrinter* solver, Stream& stream) :
		ConstraintAdditionMonitor<Stream>(solver, stream) {
}
	virtual ~RealCNFPrinter() {
	}

	void notifyStart(){
		nbconstraints = 0;
		maxvar=1;
		ss.str(std::string());
	}
	void notifyEnd(){
		ss <<"p cnf " <<maxvar <<" " <<nbconstraints <<"\n";
		target() <<ss.str();
		target().flush();
	}

	std::string toString(const Lit& lit){
		std::stringstream ss;
		ss <<(sign(lit)?"-":"") <<(var(lit)+1);
		return ss.str();
	}

	void visit(const Disjunction& clause) {
		for (uint i = 0; i < clause.literals.size(); ++i) {
			if(maxvar<var(clause.literals[i])){
				maxvar = var(clause.literals[i]);
			}
			target() <<toString(clause.literals[i]) << " ";
		}
		nbconstraints++;
		target() << "0\n";
	}

	void visit(const Rule&) {
		throw idpexception("Not supported in CNF.");
	}

	void visit(const WLSet&) {
		throw idpexception("Not supported in CNF.");
	}

	void visit(const Aggregate&) {
		throw idpexception("Not supported in CNF.");
	}

	void visit(const Implication&) {
		throw idpexception("Not supported in CNF.");
	}
	void visit(const MinimizeOrderedList&) {
		throw idpexception("Not supported in CNF.");
	}
	void visit(const MinimizeSubset&) {
		throw idpexception("Not supported in CNF.");
	}
	void visit(const MinimizeAgg&) {
		throw idpexception("Not supported in CNF.");
	}
	void visit(const MinimizeVar&) {
		throw idpexception("Not supported in CNF.");
	}
	void visit(const Symmetry&) {
		throw idpexception("Not supported in CNF.");
	}
	void visit(const IntVarRange&) {
		throw idpexception("Not supported in CNF.");
	}
	void visit(const IntVarEnum&) {
		throw idpexception("Not supported in CNF.");
	}
	void visit(const CPAllDiff&) {
		throw idpexception("Not supported in CNF.");
	}
	void visit(const CPBinaryRel&) {
		throw idpexception("Not supported in CNF.");
	}
	void visit(const CPCount&) {
		throw idpexception("Not supported in CNF.");
	}
	void visit(const CPBinaryRelVar&) {
		throw idpexception("Not supported in CNF.");
	}
	void visit(const CPSumWeighted&) {
		throw idpexception("Not supported in CNF.");
	}
};

}

#endif //AREALECNFPRINTER_HPP_
