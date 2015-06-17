/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Marien, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */

#ifndef AREALECNFPRINTER_HPP_
#define AREALECNFPRINTER_HPP_

#include "ConstraintVisitor.hpp"
#include "datastructuremacros.hpp"
#include "ExternalPrint.hpp"

namespace MinisatID {

template<typename Stream>
class RealECNFPrinter: public ConstraintStreamPrinter<Stream> {
private:
	bool remap;
	using ConstraintStreamPrinter<Stream>::target;
	using ConstraintPrinter::getPrinter;
public:
	RealECNFPrinter(LiteralPrinter* solver, Stream& stream, bool remap = true)
			: 	ConstraintStreamPrinter<Stream>(solver, stream, "ecnfprinter"),
				remap(remap) {
	}
	virtual ~RealECNFPrinter() {
	}

	void notifyStart() {
		target() << "p ecnf\n";
	}

	void notifyEnd() {
		// TODO printTranslation(ss, printedvars);
		target().flush();
	}

	std::string toString(VarID id) {
		if (remap) {
			return getPrinter()->toString(id);
		} else {
			std::stringstream ss;
			ss << id.id;
			return ss.str();
		}
	}
	std::string toString(const Lit& lit) {
		if (remap) {
			return getPrinter()->toString(lit);
		} else {
			std::stringstream ss;
			ss << (sign(lit) ? "-" : "") << (var(lit) + 1);
			return ss.str();
		}
	}

	void add(const Disjunction& clause) {
		for (uint i = 0; i < clause.literals.size(); ++i) {
			target() << toString(clause.literals[i]) << " ";
		}
		target() << "0\n";
	}

	void add(const Rule& rule) {
		target() << (rule.conjunctive ? "C" : "D") << " " << rule.definitionID << " | " << toString(mkPosLit(rule.head)) << " <- ";
		for (uint i = 0; i < rule.body.size(); ++i) {
			target() << toString(rule.body[i]) << " ";
		}
		target() << "0\n";
	}

	void add(const WLSet& set) {
		target() << WSETSTR << " " << set.setID << " ";
		for (uint i = 0; i < set.wl.size(); ++i) {
			target() << toString(set.wl[i].getLit()) << "=" << set.wl[i].getWeight() << " ";
		}
		target() << "0\n";
	}

	void add(const Aggregate& agg) {
		target() << agg.type;
		switch (agg.sem) {
		case AggSem::DEF:
			target() << "D";
			break;
		case AggSem::COMP:
			target() << "C";
			break;
		case AggSem::OR:
			target() << "O";
			break;
		}

		target() << (agg.sign == AggSign::UB ? "L" : "G") << " " << toString(agg.head) << " " << agg.setID << " " << agg.bound << " 0\n";
	}

	void add(const Implication& impl) {
		target() << IMPLICATIONSTR << " " << (impl.conjunction ? "C" : "D") << toString(impl.head) << impl.type << " ";
		for (auto l : impl.body) {
			target() << toString(l) << " ";
		}
		target() << "0\n";
	}

	void add(const MinimizeSubset& mnm) {
		target() << SUBMNMSTR << " ";
		for (auto i = mnm.literals.cbegin(); i < mnm.literals.cend(); ++i) {
			target() << toString(*i) << " ";
		}
		target() << "0\n";
	}

	void add(const MinimizeAgg& mnm) {
		target() << AGGMNMSTR << " " << mnm.type << " " << mnm.setid << " 0\n";
	}

	void add(const OptimizeVar& mnm) {
		if(mnm.minimize){
			target() << VARMNMSTR << " " << toString(mnm.varID) << " 0\n";
		}else{
			target() << VARMXMSTR << " " << toString(mnm.varID) << " 0\n";
		}
	}

	void add(const IntVarRange& range) {
		if(range.partial){
			target() <<PARTIALSTR <<" ";
		}
		target() << INTVARRANGESTR << " " <<toString(range.varID) <<" ";
		if(range.partial){
			target() <<toString(range.possiblynondenoting) <<" ";
		}
		target() << range.minvalue << " " << range.maxvalue << " 0\n";
	}

	void add(const IntVarEnum& intvar) {
		if(intvar.partial){
			target() <<PARTIALSTR <<" ";
		}
		target() << INTVARENUMSTR << " " <<toString(intvar.varID) << " ";
		if(intvar.partial){
			target() <<toString(intvar.possiblynondenoting) <<" ";
		}
		for (auto i = intvar.values.cbegin(); i < intvar.values.cend(); ++i) {
			target() << *i << " ";
		}
		target() << DELIMSTR << " 0\n";
	}

	void add(const CPAllDiff& alldiff) {
		target() << CPDISTINCTSTR << " ";
		for (auto varid : alldiff.varIDs) {
			target() << toString(varid) << " ";
		}
		target() << DELIMSTR << " 0\n";
	}

	void add(const CPBinaryRel& binconstr) {
		target() << CPBININTSTR << " " << toString(binconstr.head) << " " << toString(binconstr.varID) << " " << binconstr.rel << " " << binconstr.bound
				<< " 0\n";
	}

	void add(const CPBinaryRelVar& binconstr) {
		target() << CPBINVARSTR << " " << toString(binconstr.head) << " " << toString(binconstr.lhsvarID) << " " << binconstr.rel << " "
				<< toString(binconstr.rhsvarID) << " 0\n";
	}

	void add(const CPSumWeighted& sum) {
		target() << CPSUMSTR << " " << toString(sum.head) << " ";
		for (auto c : sum.conditions) {
			target() << toString(c) << " ";
		}
		target() << DELIMSTR << " ";
		for (auto i = sum.varIDs.cbegin(); i < sum.varIDs.cend(); ++i) {
			target() << toString(*i) << " ";
		}
		target() << DELIMSTR;
		for (auto i = sum.weights.cbegin(); i < sum.weights.cend(); ++i) {
			target() << *i << " ";
		}
		target() << sum.rel << " " << sum.bound << " 0\n";
	}

	void add(const CPProdWeighted& prod) {
		target() << CPPRODSTR << " " << toString(prod.head) << " ";
		for (auto c : prod.conditions) {
			target() << toString(c) << " ";
		}
		target() << DELIMSTR << " ";
		for (auto i = prod.varIDs.cbegin(); i < prod.varIDs.cend(); ++i) {
			target() << toString(*i) << " ";
		}
		target() << DELIMSTR << " " << prod.prodWeight << " " << prod.rel << " " << toString(prod.boundID) << " 0\n";
	}
};

}

#endif //AREALECNFPRINTER_HPP_
