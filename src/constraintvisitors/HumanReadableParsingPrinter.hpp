/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef ECNFPRINTER_HPP_
#define ECNFPRINTER_HPP_

#include <vector>
#include <sstream>
#include <iostream>

#include "ConstraintVisitor.hpp"
#include "utils/Utils.hpp"

namespace MinisatID{

template<typename Stream>
class HumanReadableParsingPrinter: public ConstraintAdditionMonitor<Stream> {
private:
	using ConstraintAdditionMonitor<Stream>::target;
	using ConstraintVisitor::getPrinter;
public:
	HumanReadableParsingPrinter(LiteralPrinter* solver, Stream& stream) :
		ConstraintAdditionMonitor<Stream>(solver, stream) {
}
	virtual ~HumanReadableParsingPrinter(){}

	void notifyStart(){}
	void notifyEnd(){
		target().flush();
	}

	void visit(const MinisatID::Implication& obj){
		target() <<"Added " <<toString(obj.head, getPrinter()) <<obj.type;
		this->printList(obj.body, obj.conjunction?" & ":" | ", target(), getPrinter());
		target() <<"\n";
	}

	void visit(const Disjunction& clause){
		target() <<"Added clause ";
		this->printList(clause.literals, " | ", target(), getPrinter());
		target() <<"\n";
	}

	void visit(const Rule& rule){
		target() <<"Added rule " <<toString(rule.head, getPrinter()) <<" <- ";
		if(rule.body.size()==0){
			target() <<(rule.conjunctive?"true":"false");
		}else{
			this->printList(rule.body, rule.conjunctive?" & ":" | ", target(), getPrinter());
		}
		target() <<" to definition " <<rule.definitionID <<"\n";
	}

	void visit(const WLSet& set){
		target() <<"Added non-weighted set " <<set.setID <<" = {";
		std::vector<Lit>::size_type count = 0;
		for(auto i=set.wl.cbegin(); i!=set.wl.cend(); ++i, ++count){
			target() <<toString((*i).getLit(), getPrinter()) <<"=" <<(*i).getWeight();
			if(count<set.wl.size()-1){
				target() <<", ";
			}
		}
		target() <<"}\n";
	}

	void visit(const Aggregate& agg){
		target() <<"Added aggregate " <<toString(agg.head, getPrinter()) <<" "<<(agg.sem==AggSem::COMP?"<=>":"<-");
		if(agg.sem==AggSem::DEF){
			target() <<"(" <<agg.defID <<")";
		}
		target() <<" " <<agg.type;
		target() <<"( set" <<agg.setID <<" )" <<(agg.sign==AggSign::UB?"=<":">=") <<agg.bound;
		target() <<"\n";
	}


	void visit(const MinimizeOrderedList& mnm){
		target() <<"Minimizing ordered list ";
		this->printList(mnm.literals, " < ", target(), getPrinter());
		target() <<"\n";
	}


	void visit(const MinimizeSubset& mnm){
		target() <<"Searching minimal subset of set { ";
		this->printList(mnm.literals, ", ", target(), getPrinter());
		target() <<" }\n";
	}

	void visit(const MinimizeVar& mnm){
		target() <<"Searching model with minimal value for variable " <<mnm.varID <<"\n";
	}

	void visit(const MinimizeAgg& mnm){
		target() <<"Searching model with minimal value for ";
		target() <<mnm.type <<"(set" <<mnm.setid <<")\n";
	}

	void visit(const Symmetry& symm){
		target() <<"Added symmetry:\n\t";
		bool begin = true;
		for(auto i=symm.symmetry.cbegin(); i<symm.symmetry.cend(); ++i){
			target() <<"[";
			for(auto j=i->cbegin(); j<i->cend(); ++j){
				if(not begin){
					target() <<", ";
				}
				begin = false;
				target() <<toString(*j, getPrinter());
			}
			target() <<"]";
		}
		target() <<"\n";
	}

	void visit(const IntVarEnum& var){
		target() <<"Integer variable var" <<var.varID <<" = [ ";
		printConcatBy(var.values, ", ", target());
		target() <<" ]\n";
	}

	void visit(const IntVarRange& var){
		target() <<"Added integer variable var" <<var.varID <<" = [ "<<var.minvalue <<".." <<var.maxvalue <<"]\n";
	}

	void visit(const CPAllDiff& alldiff){
		target() <<"Added alldifferent constraint: alldiff { ";
		printConcatBy(alldiff.varIDs, ", ", target());
		target() <<" }\n";
	}

	void visit(const CPBinaryRel& rel){
		target() <<"Added binary constraint " <<toString(rel.head, getPrinter()) <<" <=> var" <<rel.varID <<" "<<rel.rel <<" " <<rel.bound <<"\n";
	}

	void visit(const CPCount& obj){
		target() <<"Added count constraint: count of variables { ";
		printConcatBy(obj.varIDs, ", ", target());
		target() <<" } equal to " <<obj.eqbound <<obj.rel <<obj.rhsvar <<"\n";
	}

	void visit(const CPBinaryRelVar& rel){
		target() <<"Added binary constraint " <<toString(rel.head, getPrinter()) <<" <=> var" <<rel.lhsvarID <<" "<<rel.rel <<" var" <<rel.rhsvarID <<"\n";
	}

	void visit(const CPSumWeighted& sum){
		target() <<"Added sum constraint " <<toString(sum.head, getPrinter()) <<" <=> sum({ ";
		std::vector<int>::size_type count = 0;
		auto litit=sum.varIDs.cbegin();
		auto weightit=sum.weights.cbegin();
		for(; litit<sum.varIDs.cend(); ++count, ++litit, ++weightit){
			target() <<"var" <<*litit <<"*" <<*weightit;
			if(count<sum.varIDs.size()-1){
				target() <<", ";
			}
		}
		target() <<sum.rel <<" " <<sum.bound <<"\n";
	}

	void visit(const LazyGroundLit& lg){
		target() <<"Added lazy residual " <<toString(lg.residual, getPrinter()) <<", acting as " <<(lg.watchboth?"known":"true") <<" delay trigger.\n";
	};
};

}

#endif /* ECNFPRINTER_HPP_ */
