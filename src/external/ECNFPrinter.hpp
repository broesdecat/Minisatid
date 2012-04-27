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
#include "datastructuremacros.hpp"

namespace MinisatID {

template<typename Stream>
class RealECNFPrinter: public ConstraintStreamPrinter<Stream> {
private:
	bool remap;
	using ConstraintStreamPrinter<Stream>::target;
	using ConstraintPrinter::getPrinter;
public:
	RealECNFPrinter(LiteralPrinter* solver, Stream& stream, bool remap = false);
	virtual ~RealECNFPrinter() {
	}

	void notifyStart();
	void notifyEnd();

	std::string toString(const Lit& lit);

	void add(const Disjunction& clause);
	void add(const Rule& rule);
	void add(const WLSet& set);
	void add(const Aggregate& agg);
	void add(const Implication& impl);
	void add(const MinimizeOrderedList& mnm);
	void add(const MinimizeSubset& mnm);
	void add(const MinimizeAgg& mnm);
	void add(const MinimizeVar& mnm);
	void add(const Symmetry&);
	void add(const IntVarRange&);
	void add(const IntVarEnum&);
	void add(const CPAllDiff&);
	void add(const CPBinaryRel&);
	void add(const CPCount&);
	void add(const CPBinaryRelVar&);
	void add(const CPSumWeighted&);
	void add(const CPElement&);
};

}

#endif //AREALECNFPRINTER_HPP_
