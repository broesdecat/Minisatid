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
#include "external/datastructuremacros.hpp"

namespace MinisatID {

template<typename Stream>
class RealECNFPrinter: public ConstraintStreamPrinter<Stream> {
private:
	bool remap;
	using ConstraintStreamPrinter<Stream>::target;
	using ConstraintPrinter::getPrinter;
public:
	RealECNFPrinter(LiteralPrinter* solver, Stream& stream, bool remap = false) :
		ConstraintStreamPrinter<Stream>(solver, stream, "ecnfprinter"), remap(remap) {
}
	virtual ~RealECNFPrinter() {
	}

	void notifyStart(){
		target() <<"p ecnf\n";
	}
	void notifyEnd(){
		// TODO printTranslation(ss, printedvars);
		target().flush();
	}

	std::string toString(const Lit& lit){
		if(remap){
			return getPrinter()->toString(lit);
		}else{
			std::stringstream ss;
			ss <<(sign(lit)?"-":"") <<(var(lit)+1);
			return ss.str();
		}
	}

	void add(const Disjunction& clause) {
		for (uint i = 0; i < clause.literals.size(); ++i) {
			target() <<toString(clause.literals[i]) << " ";
		}
		target() << "0\n";
	}

	void add(const Rule& rule) {
		target() << (rule.conjunctive ? "C" : "D") <<rule.definitionID << " <- " << toString(mkPosLit(rule.head)) << " ";
		for (uint i = 0; i < rule.body.size(); ++i) {
			target() << toString(rule.body[i]) << " ";
		}
		target() << "0\n";
	}

	void add(const WLSet& set) {
		target() << "WLSet " << set.setID << " ";
		for (uint i = 0; i < set.wl.size(); ++i) {
			target() << toString(set.wl[i].getLit()) << "=" << set.wl[i].getWeight() << " ";
		}
		target() << "0\n";
	}

	void add(const Aggregate& agg) {
		target() << agg.type;
		switch(agg.sem){
		case AggSem::DEF:
			target() <<"D";
			break;
		case AggSem::COMP:
			target() <<"C";
			break;
		case AggSem::OR:
			target() <<"O";
			break;
		}

		target() <<(agg.sign == AggSign::UB ? "G" : "L") <<" " <<toString(agg.head) <<" " <<agg.setID <<" " <<agg.bound << " 0\n";
	}

	void add(const Implication& impl) {
		auto clauses = impl.getEquivalentClauses();
		for(auto i=clauses.cbegin(); i<clauses.cend(); ++i){
			add(*i);
		}
	}
	void add(const MinimizeOrderedList& mnm) {
		target() <<LISTMNMSTR <<" ";
		for(auto i=mnm.literals.cbegin(); i<mnm.literals.cend(); ++i){
			target() <<toString(*i) <<" ";
		}
		target() <<"0\n";
	}
	void add(const MinimizeSubset& mnm) {
		target() <<SUBMNMSTR <<" ";
		for(auto i=mnm.literals.cbegin(); i<mnm.literals.cend(); ++i){
			target() <<toString(*i) <<" ";
		}
		target() <<"0\n";
	}
	void add(const MinimizeAgg& mnm) {
		target() <<AGGMNMSTR <<" " <<mnm.type <<" " <<mnm.setid <<" 0\n";
	}
	void add(const MinimizeVar& mnm) {
		target() <<VARMNMSTR <<" " <<mnm.varID <<" 0\n";
	}
	void add(const Symmetry&) {
		throw idpexception("Not yet implemented printing of Symmetry."); // TODO
	}
	void add(const IntVarRange&) {
		throw idpexception("Not yet implemented printing of IntVarRange."); // TODO
	}
	void add(const IntVarEnum&) {
		throw idpexception("Not yet implemented printing of IntVarEnum."); // TODO
	}
	void add(const CPAllDiff&) {
		throw idpexception("Not yet implemented printing of CPAllDiff."); // TODO
	}
	void add(const CPBinaryRel&) {
		throw idpexception("Not yet implemented printing of CPBinaryRel."); // TODO
	}
	void add(const CPCount&) {
		throw idpexception("Not yet implemented printing of CPCount."); // TODO
	}
	void add(const CPBinaryRelVar&) {
		throw idpexception("Not yet implemented printing of CPBinaryRelVar."); // TODO
	}
	void add(const CPSumWeighted&) {
		throw idpexception("Not yet implemented printing of CPSumWeighted."); // TODO
	}
	void add(const CPElement&) {
		throw idpexception("Not yet implemented printing of CPElement."); // TODO
	}
};

}

#endif //AREALECNFPRINTER_HPP_
