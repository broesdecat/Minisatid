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
	using ConstraintVisitor::getPCSolver;
public:
	HumanReadableParsingPrinter(Stream& stream):ConstraintAdditionMonitor<Stream>(stream){}
	virtual ~HumanReadableParsingPrinter(){}

	void notifyStart(){}
	void notifyEnd(){
		target().flush();
	}

	void visit(const MinisatID::InnerImplication&){
		// TODO implement
	}

	void visit(const InnerDisjunction& clause){
		target() <<"Added clause ";
		printList(clause.literals, " | ", target(), getPCSolver());
		target() <<"\n";
	}

	void visit(const InnerRule& rule){
		target() <<"Added rule " <<print(rule.head, getPCSolver()) <<" <- ";
		if(rule.body.size()==0){
			target() <<(rule.conjunctive?"true":"false");
		}else{
			printList(rule.body, rule.conjunctive?" & ":" | ", target(), getPCSolver());
		}
		target() <<" to definition " <<rule.definitionID <<"\n";
	}

	void visit(const InnerWLSet& set){
		target() <<"Added non-weighted set " <<set.setID <<" = {";
		std::vector<Lit>::size_type count = 0;
		for(auto i=set.wls.cbegin(); i!=set.wls.cend(); ++i, ++count){
			target() <<print((*i).getLit(), getPCSolver()) <<"=" <<(*i).getWeight();
			if(count<set.wls.size()-1){
				target() <<", ";
			}
		}
		target() <<"}\n";
	}

	void visit(const InnerAggregate& agg){
		target() <<"Added aggregate: " <<agg.type;
		target() <<"( set" <<agg.setID <<" )" <<(agg.sign==AggSign::UB?"=<":">=") <<agg.bound;
		target() <<"\n";
	}

	void visit(const InnerReifAggregate& agg){
		target() <<"Added aggregate " <<print(agg.head, getPCSolver()) <<" "<<(agg.sem==AggSem::COMP?"<=>":"<-");
		if(agg.sem==AggSem::DEF){
			target() <<"(" <<agg.defID <<")";
		}
		target() <<" " <<agg.type;
		target() <<"( set" <<agg.setID <<" )" <<(agg.sign==AggSign::UB?"=<":">=") <<agg.bound;
		target() <<"\n";
	}


	void visit(const InnerMinimizeOrderedList& mnm){
		target() <<"Minimizing ordered list ";
		printList(mnm.literals, " < ", target(), getPCSolver());
		target() <<"\n";
	}


	void visit(const InnerMinimizeSubset& mnm){
		target() <<"Searching minimal subset of set { ";
		printList(mnm.literals, ", ", target(), getPCSolver());
		target() <<" }\n";
	}

	void visit(const InnerMinimizeVar& mnm){
		target() <<"Searching model with minimal value for variable " <<mnm.varID <<"\n";
	}

	void visit(const InnerMinimizeAgg& mnm){
		target() <<"Searching model with minimal value for ";
		target() <<mnm.type <<"(set" <<mnm.setID <<")\n";
	}

	void visit(const InnerSymmetry& symm){
		target() <<"Added symmetry:\n\t";
		bool begin = true;
		for(auto i=symm.symmetry.cbegin(); i!=symm.symmetry.cend(); ++i){
			if(not begin){
				target() <<", ";
			}
			begin = false;
			target() <<print((*i).first, getPCSolver()) <<"->" <<print((*i).second, getPCSolver());
		}
		target() <<"\n";
	}

	void visit(const InnerForcedChoices& choices){
		target() <<"Forced choices ";
		printList(choices.forcedchoices, " ", target(), getPCSolver());
		target() <<"\n";
	}

	void visit(const InnerIntVarEnum& var){
		target() <<"Integer variable var" <<var.varID <<" = [ ";
		printConcatBy(var.values, ", ", target());
		target() <<" ]\n";
	}

	void visit(const InnerIntVarRange& var){
		target() <<"Added integer variable var" <<var.varID <<" = [ "<<var.minvalue <<".." <<var.maxvalue <<"]\n";
	}

	void visit(const InnerCPAllDiff& alldiff){
		target() <<"Added alldifferent constraint: alldiff { ";
		printConcatBy(alldiff.varIDs, ", ", target());
		target() <<" }\n";
	}

	void visit(const InnerCPBinaryRel& rel){
		target() <<"Added binary constraint " <<print(rel.head, getPCSolver()) <<" <=> var" <<rel.varID <<" "<<rel.rel <<" " <<rel.bound <<"\n";
	}

	void visit(const InnerCPCount&){
		throw idpexception("Not yet implemented."); // TODO
	}

	void visit(const InnerCPBinaryRelVar& rel){
		target() <<"Added binary constraint " <<print(rel.head, getPCSolver()) <<" <=> var" <<rel.lhsvarID <<" "<<rel.rel <<" var" <<rel.rhsvarID <<"\n";
	}

	void visit(const InnerCPSumWeighted& sum){
		target() <<"Added sum constraint " <<print(sum.head, getPCSolver()) <<" <=> sum({ ";
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
};

}

#endif /* ECNFPRINTER_HPP_ */
