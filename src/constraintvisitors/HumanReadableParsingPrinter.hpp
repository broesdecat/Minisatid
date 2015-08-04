/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Marien, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#pragma once

#include <vector>
#include <sstream>
#include <iostream>

#include "external/ConstraintVisitor.hpp"
#include "utils/Utils.hpp"

namespace MinisatID {

template<typename Stream>
class HumanReadableParsingPrinter: public ConstraintStreamPrinter<Stream> {
private:
	using ConstraintStreamPrinter<Stream>::target;
	using ConstraintPrinter::getPrinter;
public:
	HumanReadableParsingPrinter(LiteralPrinter* solver, Stream& stream)
			: ConstraintStreamPrinter<Stream>(solver, stream, "humanreadableprinter") {
	}
	virtual ~HumanReadableParsingPrinter() {
	}

	void notifyStart() {
	}
	void notifyEnd() {
		target().flush();
	}

	template<class Elem>
	std::string print(const Elem& id) {
		return toString(id, *getPrinter());
	}

	template<class Elem>
	struct Print {
	private:
		LiteralPrinter* printer;
	public:
		Print(LiteralPrinter* printer)
				: printer(printer) {

		}
		std::string operator()(const Elem& elem) {
			return toString(elem, *printer);
		}
	};

	template<typename List, typename SS, typename Functor>
	void printConcatWithFunctor(const List& list, const std::string& concat, SS& stream, Functor func) {
		bool begin = true;
		for (auto i = list.cbegin(); i < list.cend(); ++i) {
			if (not begin) {
				stream << concat;
			}
			begin = false;
			stream << func(*i);
		}
	}

	void add(const MinisatID::Implication& obj) {
		target() << "Added " << print(obj.head) << obj.type;
		printConcatWithFunctor(obj.body, obj.conjunction ? " & " : " | ", target(), Print<Lit>(getPrinter()));
		target() << "\n";
	}

	void add(const Disjunction& clause) {
		target() << "Added clause ";
		printConcatWithFunctor(clause.literals, " | ", target(), Print<Lit>(getPrinter()));
		target() << "\n";
	}

	void add(const Rule& rule) {
		target() << "Added rule " << print(rule.head) << " <- ";
		if (rule.body.size() == 0) {
			target() << (rule.conjunctive ? "true" : "false");
		} else {
			printConcatWithFunctor(rule.body, rule.conjunctive ? " & " : " | ", target(), Print<Lit>(getPrinter()));
		}
		target() << " to definition " << rule.definitionID << "\n";
	}

	void add(const WLSet& set) {
		target() << "Added weighted set " << set.setID << " = {";
		std::vector<Lit>::size_type count = 0;
		for (auto i = set.wl.cbegin(); i != set.wl.cend(); ++i, ++count) {
			target() << print((*i).getLit()) << "=" << (*i).getWeight();
			if (count < set.wl.size() - 1) {
				target() << ", ";
			}
		}
		target() << "}\n";
	}

	void add(const Aggregate& agg) {
		target() << "Added aggregate " << print(agg.head) << " ";
		switch (agg.sem) {
		case AggSem::COMP:
			target() << "<=>";
			break;
		case AggSem::DEF:
			target() << "<-" << "(" << agg.defID << ")";
			break;
		case AggSem::OR:
			target() << "|";
			break;
		}
		target() << " " << agg.type;
		target() << "( set" << agg.setID << " )" << (agg.sign == AggSign::UB ? "=<" : ">=") << agg.bound;
		target() << "\n";
	}

	void add(const MinimizeSubset& mnm) {
		target() << "Searching minimal subset of set { ";
		printConcatWithFunctor(mnm.literals, ", ", target(), Print<Lit>(getPrinter()));
		target() << " }\n";
	}

	void add(const OptimizeVar& mnm) {
		target() << "Searching model with " <<(mnm.minimize?"minimal":"maximal") <<" value for variable " << print(mnm.varID) << "\n";
	}

	void add(const MinimizeAgg& mnm) {
		target() << "Searching model with minimal value for ";
		target() << mnm.type << "(set" << mnm.setid << ")\n";
	}

	void add(const IntVarEnum& var) {
		target() << "Added integer variable " << print(var.varID) << " = { ";
		printConcatBy(var.values, ", ", target());
		if(var.partial){
			target() <<", novalue if " <<print(var.possiblynondenoting);
		}
		target() << " }\n";
	}

	void add(const IntVarRange& var) {
		target() << "Added integer variable " << print(var.varID) << " = [ " << var.minvalue << ".." << var.maxvalue << " ]";
		if(var.partial){
			target() <<", novalue if " <<print(var.possiblynondenoting) <<"\n";
		}
		target() <<"\n";
	}

	void add(const CPAllDiff& alldiff) {
		target() << "Added alldifferent constraint: alldiff { ";
		printConcatWithFunctor(alldiff.varIDs, ", ", target(), Print<VarID>(getPrinter()));
		target() << " }\n";
	}

	void add(const CPBinaryRel& rel) {
		target() << "Added binary constraint " << print(rel.head) << " <=> " << print(rel.varID) << " " << rel.rel << " " << rel.bound << "\n";
	}

	void add(const CPBinaryRelVar& rel) {
		target() << "Added binary constraint " << print(rel.head) << " <=> " << print(rel.lhsvarID) << " " << rel.rel << " " << print(rel.rhsvarID)
				<< "\n";
	}

	void add(const CPSumWeighted& sum) {
		target() << "Added sum constraint " << print(sum.head) << " <=> sum({ ";
		bool begin = true;
		for(uint i=0; i<sum.varIDs.size(); ++i){
			if (not begin) {
				target() << ", ";
			}
			begin = false;
			target() << "if " << print(sum.conditions[i]) << " " << print(sum.varIDs[i]) << "*" << sum.weights[i];
		}
		target() << " }) " << sum.rel << " " << sum.bound << "\n";
	}

	void add(const CPProdWeighted& prod) {
		target() << "Added product constraint " << print(prod.head) << " <=> ";
		target() << prod.prodWeight << " * ";
		target() << "prod({ ";
		bool begin = true;
		for(uint i=0; i<prod.varIDs.size(); ++i){
			if (not begin) {
				target() << ", ";
			}
			begin = false;
			target() << "if " << print(prod.conditions[i]) << " " << print(prod.varIDs[i]);
		}
		target() << " }) " << prod.rel << " " << print(prod.boundID) << "\n";
	}

	void add(const LazyGroundLit& lg) {
		target() << "Added lazy residual " << print(lg.residual) << ", acting as " << lg.watchedvalue << " delay trigger.\n";
	}

	void add(const TwoValuedRequirement& lg) {
		target() << "Atoms ";
		for(auto a:lg.atoms){
			target()<<print(a) <<" ";
		}
		target() <<" should be two-valued in any model.\n";
	}

	void add(const TwoValuedVarIdRequirement& lg) {
		target() << "VarId " << print(lg.vid) << " should be two-valued in any model.\n";
	}

	virtual void add(const LazyGroundImpl& lg) {
		target() << "Added lazy " << (lg.impl.conjunction ? "conjunctive" : "disjunctive") << " implication " << ": " << print(lg.impl.head) << " "
				<< lg.impl.type;
		printConcatWithFunctor(lg.impl.body, lg.impl.conjunction ? " & " : " | ", target(), Print<Lit>(getPrinter()));
		if (lg.impl.body.size() > 0) {
			target() << (lg.impl.conjunction ? " & " : " | ");
		}
		target() << " lazy_tseitin\n";
	}
	virtual void add(const LazyAddition& lg) {
		target() << "Added literals ";
		printConcatWithFunctor(lg.list, " ", target(), Print<Lit>(getPrinter()));
		target() << " to lazy implication " << lg.ref << "\n";
	}
	virtual void add(const SubTheory& subtheory) {
		target() << "Created subtheory " << subtheory.childid.id << "\n";
		// FIXME implement rest and add printing of theoryids to other add methods
	}

	void add(const LazyAtom& lg) {
		target() << "Added lazy element constraint with head " << print(lg.head) << " <=> ";
		target() << lg.grounder->getSymbolName() << "(";
		bool begin = true;
		for (auto v : lg.args) {
			if (not begin) {
				target() << ", ";
			}
			begin = false;
			target() << print(v);
		}
		target() << ").\n"; // TODO known arguments are not printed here
	}
};

}
