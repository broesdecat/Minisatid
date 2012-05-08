/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */

#include "external/ECNFPrinter.hpp"
#include "external/ConstraintVisitor.hpp"
#include "utils/Utils.hpp"
#include "utils/Print.hpp"
#include "external/datastructuremacros.hpp"

using namespace MinisatID;
using namespace std;

template<typename Stream>
RealECNFPrinter<Stream>::RealECNFPrinter(LiteralPrinter* solver, Stream& stream, bool remap)
		: 	ConstraintStreamPrinter<Stream>(solver, stream, "ecnfprinter"),
			remap(remap) {
}

template<typename Stream>
void RealECNFPrinter<Stream>::notifyStart() {
	target() << "p ecnf\n";
}
template<typename Stream>
void RealECNFPrinter<Stream>::notifyEnd() {
	// TODO printTranslation(ss, printedvars);
	target().flush();
}

template<typename Stream>
std::string RealECNFPrinter<Stream>::toString(const Lit& lit) {
	if (remap) {
		return getPrinter()->toString(lit);
	} else {
		std::stringstream ss;
		ss << (sign(lit) ? "-" : "") << (var(lit) + 1);
		return ss.str();
	}
}

template<typename Stream>
void RealECNFPrinter<Stream>::add(const Disjunction& clause) {
	for (uint i = 0; i < clause.literals.size(); ++i) {
		target() << toString(clause.literals[i]) << " ";
	}
	target() << "0\n";
}

template<typename Stream>
void RealECNFPrinter<Stream>::add(const Rule& rule) {
	target() << (rule.conjunctive ? "C" : "D") << rule.definitionID << " <- " << toString(mkPosLit(rule.head)) << " ";
	for (uint i = 0; i < rule.body.size(); ++i) {
		target() << toString(rule.body[i]) << " ";
	}
	target() << "0\n";
}

template<typename Stream>
void RealECNFPrinter<Stream>::add(const WLSet& set) {
	target() << WSETSTR <<" " << set.setID << " ";
	for (uint i = 0; i < set.wl.size(); ++i) {
		target() << toString(set.wl[i].getLit()) << "=" << set.wl[i].getWeight() << " ";
	}
	target() << "0\n";
}

template<typename Stream>
void RealECNFPrinter<Stream>::add(const Aggregate& agg) {
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

	target() << (agg.sign == AggSign::UB ? "G" : "L") << " " << toString(agg.head) << " " << agg.setID << " " << agg.bound << " 0\n";
}

template<typename Stream>
void RealECNFPrinter<Stream>::add(const Implication& impl) {
	auto clauses = impl.getEquivalentClauses();
	for (auto i = clauses.cbegin(); i < clauses.cend(); ++i) {
		add(*i);
	}
}
template<typename Stream>
void RealECNFPrinter<Stream>::add(const MinimizeOrderedList& mnm) {
	target() << LISTMNMSTR <<" ";
	for (auto i = mnm.literals.cbegin(); i < mnm.literals.cend(); ++i) {
		target() << toString(*i) << " ";
	}
	target() << "0\n";
}
template<typename Stream>
void RealECNFPrinter<Stream>::add(const MinimizeSubset& mnm) {
	target() << SUBMNMSTR <<" ";
	for (auto i = mnm.literals.cbegin(); i < mnm.literals.cend(); ++i) {
		target() << toString(*i) << " ";
	}
	target() << "0\n";
}
template<typename Stream>
void RealECNFPrinter<Stream>::add(const MinimizeAgg& mnm) {
	target() << AGGMNMSTR <<" " << mnm.type << " " << mnm.setid << " 0\n";
}
template<typename Stream>
void RealECNFPrinter<Stream>::add(const MinimizeVar& mnm) {
	target() << VARMNMSTR <<" " << mnm.varID << " 0\n";
}
template<typename Stream>
void RealECNFPrinter<Stream>::add(const Symmetry& symm) {
	target() << "[";
	bool symmbegin = true;
	for (auto i = symm.symmetry.cbegin(); i < symm.symmetry.cend(); ++i) {
		if (not symmbegin) {
			target() << ", ";
		}
		symmbegin = false;
		target() << "(";
		bool cyclebegin = true;
		for (auto j = (*i).cbegin(); j < (*i).cend(); ++j) {
			if (not cyclebegin) {
				target() << ", ";
			}
			cyclebegin = false;
			target() << toString(*j) << " ";
		}
		target() << ")";
	}
	target() << "]\n";
}
template<typename Stream>
void RealECNFPrinter<Stream>::add(const IntVarRange& range) {
	target() << INTVARRANGESTR <<" " << range.varID << " " << range.minvalue << " " << range.maxvalue << " 0\n";
}
template<typename Stream>
void RealECNFPrinter<Stream>::add(const IntVarEnum& intvar) {
	target() << INTVARRANGESTR <<" " << intvar.varID << " ";
	for (auto i = intvar.values.cbegin(); i < intvar.values.cend(); ++i) {
		target() << *i << " ";
	}
	target() << DELIMSTR <<" 0\n";
}
template<typename Stream>
void RealECNFPrinter<Stream>::add(const CPAllDiff& alldiff) {
	target() << CPDISTINCTSTR <<" ";
	for (auto i = alldiff.varIDs.cbegin(); i < alldiff.varIDs.cend(); ++i) {
		target() << *i << " ";
	}
	target() << DELIMSTR <<" 0\n";
}
template<typename Stream>
void RealECNFPrinter<Stream>::add(const CPBinaryRel& binconstr) {
	target() <<CPBININTSTR <<" " <<toString(mkPosLit(binconstr.head)) <<" " <<binconstr.varID <<" " <<binconstr.rel <<" " <<binconstr.bound <<" 0\n";
}
template<typename Stream>
void RealECNFPrinter<Stream>::add(const CPBinaryRelVar& binconstr) {
	target() <<CPBINVARSTR <<" " <<toString(mkPosLit(binconstr.head)) <<" " <<binconstr.rhsvarID <<" " <<binconstr.rel <<" " <<binconstr.rhsvarID <<" 0\n";
}
template<typename Stream>
void RealECNFPrinter<Stream>::add(const CPCount& count) {
	target() << CPCOUNTSTR <<" ";
	for (auto i = count.varIDs.cbegin(); i < count.varIDs.cend(); ++i) {
		target() << *i << " ";
	}
	target() <<DELIMSTR <<count.eqbound <<" " <<count.rel <<" " <<count.rhsvar <<" 0\n";
}
template<typename Stream>
void RealECNFPrinter<Stream>::add(const CPSumWeighted& sum) {
	target() << CPSUMSTR <<" " <<toString(mkPosLit(sum.head)) <<" ";
	for (auto i = sum.varIDs.cbegin(); i < sum.varIDs.cend(); ++i) {
		target() << *i << " ";
	}
	target() <<DELIMSTR;
	for (auto i = sum.weights.cbegin(); i < sum.weights.cend(); ++i) {
		target() << *i << " ";
	}
	target() <<sum.rel <<" " <<sum.bound <<" 0\n";
}
template<typename Stream>
void RealECNFPrinter<Stream>::add(const CPElement& elem) {
	target() << CPELEMENTSTR <<" ";
	for (auto i = elem.varIDs.cbegin(); i < elem.varIDs.cend(); ++i) {
		target() << *i << " ";
	}
	target() <<DELIMSTR <<elem.index <<" " <<elem.rhs <<" 0\n";
}

// Explicit instantiations. Note, apparently, they have to be AT THE END of the cpp
template class MinisatID::RealECNFPrinter<std::ostream> ;
