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

#include "parser/parsingmonitors/ParsingMonitor.hpp"
#include "utils/Utils.hpp"

namespace MinisatID{

class HumanReadableParsingPrinter: public ParsingMonitor {
public:
	HumanReadableParsingPrinter(std::ostream& stream):ParsingMonitor(stream){}
	virtual ~HumanReadableParsingPrinter(){}

	void notifyadded(const InnerDisjunction& clause){
		target() <<"Added clause ";
		for(uint i=0; i<clause.literals.size(); ++i){
			target() <<clause.literals[i];
			if(i<clause.literals.size()-1){
				target() <<" | ";
			}
		}
		target() <<"\n";
	}

	void notifyadded(const InnerRule& rule){
		target() <<"Added rule " <<getPrintableVar(rule.head) <<" <- ";
		for(uint i=0; i<rule.body.size(); ++i){
			target() <<rule.body[i];
			if(i<rule.body.size()-1){
				if(rule.conjunctive){
					target() <<" & ";
				}else{
					target() <<" | ";
				}
			}
		}
		target() <<" to definition " <<rule.definitionID <<"\n";
	}

	void notifyadded(const InnerWLSet& set){
		target() <<"Added non-weighted set " <<set.setID <<" = {";
		std::vector<Lit>::size_type count = 0;
		for(auto i=set.wls.cbegin(); i!=set.wls.cend(); ++i, ++count){
			target() <<(*i).getLit() <<"=" <<(*i).getWeight();
			if(count<set.wls.size()-1){
				target() <<", ";
			}
		}
		target() <<"}\n";
	}

	void notifyadded(const InnerAggregate& agg){
		target() <<"Added aggregate: ";
		switch(agg.type){
		case SUM:
			target() <<"sum";
			break;
		case CARD:
			target() <<"card";
			break;
		case MIN:
			target() <<"min";
			break;
		case MAX:
			target() <<"max";
			break;
		case PROD:
			target() <<"prod";
			break;
		}
		target() <<"( set" <<agg.setID <<" )" <<(agg.sign==AGGSIGN_UB?"=<":">=") <<agg.bound;
		target() <<"\n";
	}

	void notifyadded(const InnerReifAggregate& agg){
		target() <<"Added aggregate " << getPrintableVar(agg.head) <<" "<<(agg.sem==COMP?"<=>":"<-");
		if(agg.sem==DEF){
			target() <<"(" <<agg.defID <<")";
		}
		target() <<" ";
		switch(agg.type){
		case SUM:
			target() <<"sum";
			break;
		case CARD:
			target() <<"card";
			break;
		case MIN:
			target() <<"min";
			break;
		case MAX:
			target() <<"max";
			break;
		case PROD:
			target() <<"prod";
			break;
		}
		target() <<"( set" <<agg.setID <<" )" <<(agg.sign==AGGSIGN_UB?"=<":">=") <<agg.bound;
		target() <<"\n";
	}


	void notifyadded(const InnerMinimizeOrderedList& mnm){
		target() <<"Minimizing ordered list ";
		for(uint i=0; i<mnm.literals.size(); ++i){
			target() <<mnm.literals[i];
			if(i<mnm.literals.size()-1){
				target() <<" < ";
			}
		}
		target() <<"\n";
	}


	void notifyadded(const InnerMinimizeSubset& mnm){
		target() <<"Searching minimal subset of set { ";
		for(uint i=0; i<mnm.literals.size(); ++i){
			target() <<mnm.literals[i];
			if(i<mnm.literals.size()-1){
				target() <<",";
			}
		}
		target() <<" }\n";
	}

	void notifyadded(const InnerSymmetry& symm){
		target() <<"Added symmetry:\n\t";
		bool begin = true;
		for(auto i=symm.symmetry.cbegin(); i!=symm.symmetry.cend(); ++i){
			if(not begin){
				target() <<", ";
			}
			begin = false;
			target() <<(*i).first <<"->" <<(*i).second;
		}
		target() <<"\n";
	}

	void notifyadded(const InnerSymmetryLiterals& symm){
		target() <<"Added symmetries:\n";
		for(vsize i=0; i<symm.literalgroups.size(); ++i){
			target() <<"\tgroup ";
			for(vsize j=0; j<symm.literalgroups[i].size(); ++j){
				target() <<symm.literalgroups[i][j] <<" ";
			}
			target() <<"\n";
		}
	}


	void notifyadded(const InnerForcedChoices& choices){
		target() <<"Forced choices ";
		for(uint i=0; i<choices.forcedchoices.size(); ++i){
			target() <<choices.forcedchoices[i];
			if(i<choices.forcedchoices.size()-1){
				target() <<" ";
			}
		}
		target() <<"\n";
	}


	void notifyadded(const InnerIntVarEnum& var){
		target() <<"Integer variable var" <<var.varID <<" = [ ";
		for(uint i=0; i<var.values.size(); ++i){
			target() <<var.values[i];
			if(i<var.values.size()-1){
				target() <<", ";
			}
		}
		target() <<" ]\n";
	}


	void notifyadded(const InnerIntVarRange& var){
		target() <<"Added integer variable var" <<var.varID <<" = [ "<<var.minvalue <<".." <<var.maxvalue <<"]\n";
	}


	void notifyadded(const InnerCPAllDiff& alldiff){
		target() <<"Added alldifferent constraint: alldiff { ";
		for(uint i=0; i<alldiff.varIDs.size(); ++i){
			target() <<"var" <<alldiff.varIDs[i];
			if(i<alldiff.varIDs.size()-1){
				target() <<", ";
			}
		}
		target() <<" }\n";
	}


	void notifyadded(const InnerCPBinaryRel& rel){
		target() <<"Added binary constraint " <<getPrintableVar(rel.head) <<" <=> var" <<rel.varID <<" "<<rel.rel <<" " <<rel.bound <<"\n";
	}


	void notifyadded(const InnerCPCount& set){

	}


	void notifyadded(const InnerCPBinaryRelVar& rel){
		target() <<"Added binary constraint " <<getPrintableVar(rel.head) <<" <=> var" <<rel.lhsvarID <<" "<<rel.rel <<" var" <<rel.rhsvarID <<"\n";
	}


	void notifyadded(const InnerCPSumWeighted& sum){
		target() <<"Added sum constraint " <<getPrintableVar(sum.head) <<" <=> sum({ ";
		std::vector<int>::size_type count = 0;
		std::vector<uint>::const_iterator litit=sum.varIDs.cbegin();
		std::vector<Weight>::const_iterator weightit=sum.weights.cbegin();
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
