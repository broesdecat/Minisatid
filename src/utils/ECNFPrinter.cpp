/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#include "utils/ECNFPrinter.hpp"
#include "utils/Print.hpp"

using namespace std;
using namespace MinisatID;

ECNFPrinter::ECNFPrinter() {}

ECNFPrinter::~ECNFPrinter() {}

void ECNFPrinter::startPrinting(){
}

template<>
void ECNFPrinter::notifyadded(const InnerDisjunction& clause){
	ss <<"Added clause ";
	for(int i=0; i<clause.literals.size(); ++i){
		ss <<clause.literals[i];
		if(i<clause.literals.size()-1){
			ss <<" | ";
		}
	}
	ss <<"\n";
}

template<>
void ECNFPrinter::notifyadded(const InnerRule& rule){
	ss <<"Added rule: " <<getPrintableVar(rule.head) <<" <- ";
	for(int i=0; i<rule.body.size(); ++i){
		ss <<rule.body[i];
		if(i<rule.body.size()-1){
			if(rule.conjunctive){
				ss <<" & ";
			}else{
				ss <<" | ";
			}
		}
	}
	ss <<"\n";
}

template<>
void ECNFPrinter::notifyadded(const InnerSet& set){
	ss <<"Added non-weighted set " <<set.setID <<" = {";
	vector<Lit>::size_type count = 0;
	for(vector<Lit>::const_iterator i=set.literals.cbegin(); i<set.literals.cend(); ++i, ++count){
		ss <<*i;
		if(count<set.literals.size()-1){
			ss <<", ";
		}
	}
	ss <<"}\n";
}

template<>
void ECNFPrinter::notifyadded(const InnerWSet& set){
	ss <<"Added non-weighted set " <<set.setID <<" = {";
	vector<Lit>::size_type count = 0;
	vector<Lit>::const_iterator litit = set.literals.cbegin();
	vector<Weight>::const_iterator weightit = set.weights.cbegin();
	for(; litit<set.literals.cend(); ++litit, ++weightit, ++count){
		ss <<*litit <<"=" <<*weightit;
		if(count<set.literals.size()-1){
			ss <<", ";
		}
	}
	ss <<"}\n";
}

template<>
void ECNFPrinter::notifyadded(const InnerAggregate& agg){
	ss <<"Added aggregate " << agg.head <<" "<<(agg.sem==COMP?"<=>":"<-");
	if(agg.sem==DEF){
		ss <<"(" <<agg.defID <<")";
	}
	ss <<" ";
	switch(agg.type){
	case SUM:
		ss <<"sum";
		break;
	case CARD:
		ss <<"card";
		break;
	case MIN:
		ss <<"min";
		break;
	case MAX:
		ss <<"max";
		break;
	case PROD:
		ss <<"prod";
		break;
	}
	ss <<"( set" <<agg.setID <<" )" <<(agg.sign==AGGSIGN_UB?"=<":">=") <<agg.bound;
	ss <<"\n";
}

template<>
void ECNFPrinter::notifyadded(const InnerMinimizeAgg& mnm){
	ss <<"Minimizing aggregate " <<mnm.head <<" <=> ";
	switch(mnm.type){
	case SUM:
		ss <<"sum";
		break;
	case CARD:
		ss <<"card";
		break;
	case MIN:
		ss <<"min";
		break;
	case MAX:
		ss <<"max";
		break;
	case PROD:
		ss <<"prod";
		break;
	}
	ss <<"( set" <<mnm.setID <<" )";
}

template<>
void ECNFPrinter::notifyadded(const InnerMinimizeOrderedList& mnm){
	ss <<"Minimizing ordered list ";
	for(int i=0; i<mnm.literals.size(); ++i){
		ss <<mnm.literals[i];
		if(i<mnm.literals.size()-1){
			ss <<" < ";
		}
	}
	ss <<"\n";
}

template<>
void ECNFPrinter::notifyadded(const InnerMinimizeSubset& mnm){
	ss <<"Searching minimal subset of set { ";
	for(int i=0; i<mnm.literals.size(); ++i){
		ss <<mnm.literals[i];
		if(i<mnm.literals.size()-1){
			ss <<",";
		}
	}
	ss <<" }\n";
}

template<>
void ECNFPrinter::notifyadded(const InnerSymmetryLiterals& symm){
	ss <<"Added symmetries:\n";
	for(int i=0; i<symm.literalgroups.size(); ++i){
		ss <<"\tgroup ";
		for(int j=0; j<symm.literalgroups[i].size(); ++j){
			ss <<symm.literalgroups[i][j] <<" ";
		}
		ss <<"\n";
	}
}

template<>
void ECNFPrinter::notifyadded(const InnerSymmetry& symm){
	ss <<"Added symmetry: <";
	bool begin = true;
	for(auto i=symm.symmetry.cbegin(); i!=symm.symmetry.cbegin(); ++i){
		if(!begin){
			ss <<", ";
		}
		begin = false;
		ss <<(*i).first <<"->" <<(*i).second;
	}
	ss <<">\n";
}

template<>
void ECNFPrinter::notifyadded(const InnerForcedChoices& choices){
	ss <<"Forced choices ";
	for(int i=0; i<choices.forcedchoices.size(); ++i){
		ss <<choices.forcedchoices[i];
		if(i<choices.forcedchoices.size()-1){
			ss <<" ";
		}
	}
	ss <<"\n";
}

template<>
void ECNFPrinter::notifyadded(const InnerIntVarEnum& var){
	ss <<"Integer variable var" <<var.varID <<" = [ ";
	for(uint i=0; i<var.values.size(); ++i){
		ss <<var.values[i];
		if(i<var.values.size()-1){
			ss <<", ";
		}
	}
	ss <<" ]\n";
}

template<>
void ECNFPrinter::notifyadded(const InnerIntVarRange& var){
	ss <<"Added integer variable var" <<var.varID <<" = [ "<<var.minvalue <<".." <<var.maxvalue <<"]\n";
}

template<>
void ECNFPrinter::notifyadded(const InnerCPAllDiff& alldiff){
	ss <<"Added alldifferent constraint: alldiff { ";
	for(uint i=0; i<alldiff.varIDs.size(); ++i){
		ss <<"var" <<alldiff.varIDs[i];
		if(i<alldiff.varIDs.size()-1){
			ss <<", ";
		}
	}
	ss <<" }\n";
}

template<>
void ECNFPrinter::notifyadded(const InnerCPBinaryRel& rel){
	ss <<"Added binary constraint " <<rel.head <<" <=> var" <<rel.varID <<" "<<rel.rel <<" " <<rel.bound <<"\n";
}

template<>
void ECNFPrinter::notifyadded(const InnerCPCount& set){

}

template<>
void ECNFPrinter::notifyadded(const InnerCPBinaryRelVar& rel){
	ss <<"Added binary constraint " <<rel.head <<" <=> var" <<rel.lhsvarID <<" "<<rel.rel <<" var" <<rel.rhsvarID <<"\n";
}

template<>
void ECNFPrinter::notifyadded(const InnerCPSumWeighted& sum){
	ss <<"Added sum constraint " <<sum.head <<" <=> sum({ ";
	vector<int>::size_type count = 0;
	vector<uint>::const_iterator litit=sum.varIDs.cbegin();
	vector<Weight>::const_iterator weightit=sum.weights.cbegin();
	for(; litit<sum.varIDs.cend(); ++count, ++litit, ++weightit){
		ss <<"var" <<*litit <<"*" <<*weightit;
		if(count<sum.varIDs.size()-1){
			ss <<", ";
		}
	}
	ss <<sum.rel <<" " <<sum.bound <<"\n";
}

void ECNFPrinter::endPrinting(ostream& stream){
	stream <<ss.str();
}



/*

ECNFGraphPrinter::ECNFGraphPrinter() {}

ECNFGraphPrinter::~ECNFGraphPrinter() {}

void ECNFGraphPrinter::startPrinting(){
	ss <<"graph ecnftheory {\n";
}

template<>
void ECNFGraphPrinter::notifyadded(const InnerDisjunction& lits){
	for(int i=0; i<lits.size(); ++i){
		if(i>0){
			ss <<" -- ";
		}
		ss <<getPrintableVar(var(lits[i]));
	}
	if(lits.size()>1){
		ss <<" -- " <<getPrintableVar(var(lits[0])) <<" ";
	}
	ss <<"[color=blue];\n";
}

template<>
void ECNFGraphPrinter::notifyadded(const InnerRule& lits){
	for(int i=0; i<lits.size(); ++i){
		if(i>0){
			ss <<" -- ";
		}
		ss <<getPrintableVar(var(lits[i]));
	}
	if(lits.size()>1){
		ss <<" -- " <<getPrintableVar(var(lits[0])) <<" ";
	}
	ss <<"[color=green];\n";
}

template<>
void ECNFGraphPrinter::notifyadded(const InnerSet& lits){
	for(int i=0; i<lits.size(); ++i){
		if(i>0){
			ss <<" -- ";
		}
		ss <<getPrintableVar(var(lits[i]));
	}
	if(lits.size()>1){
		ss <<" -- " <<getPrintableVar(var(lits[0])) <<" ";
	}
	ss <<"[color=green];\n";
}

template<>
void ECNFGraphPrinter::notifyadded(const InnerWSet& lits){
	for(int i=0; i<lits.size(); ++i){
		if(i>0){
			ss <<" -- ";
		}
		ss <<getPrintableVar(var(lits[i]));
	}
	if(lits.size()>1){
		ss <<" -- " <<getPrintableVar(var(lits[0])) <<" ";
	}
	ss <<"[color=green];\n";
}

template<>
void ECNFGraphPrinter::notifyadded(const InnerAggregate& lits){
	for(int i=0; i<lits.size(); ++i){
		if(i>0){
			ss <<" -- ";
		}
		ss <<getPrintableVar(var(lits[i]));
	}
	if(lits.size()>1){
		ss <<" -- " <<getPrintableVar(var(lits[0])) <<" ";
	}
	ss <<"[color=green];\n";
}

void ECNFGraphPrinter::endPrinting(ostream& stream){
	ss <<"}\n";
	stream <<ss;
}*/
