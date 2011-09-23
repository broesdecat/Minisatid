/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef ECNFGRAPHPARSINGMONITOR_HPP_
#define ECNFGRAPHPARSINGMONITOR_HPP_

#include "parser/parsingmonitors/ParsingMonitor.hpp"

namespace MinisatID{

class ECNFGraphPrinter: public ParsingMonitor {
public:
	ECNFGraphPrinter(std::ostream& stream):ParsingMonitor(stream){}
	virtual ~ECNFGraphPrinter(){}

	virtual void notifyStart(){
		target() <<"graph ecnftheory {\n";
	}
	virtual void notifyEnd(){
		target() <<"}\n";
	}

	void notifyadded(const MinisatID::InnerDisjunction& lits){
		for(uint i=0; i<lits.literals.size(); ++i){
			if(i>0){
				target() <<" -- ";
			}
			target() <<getPrintableVar(var(lits.literals[i]));
		}
		if(lits.literals.size()>1){
			target() <<" -- " <<getPrintableVar(var(lits.literals[0])) <<" ";
		}
		target() <<"[color=blue];\n";
	}

	void notifyadded(const MinisatID::InnerRule& lits){
		for(uint i=0; i<lits.body.size(); ++i){
			if(i>0){
				target() <<" -- ";
			}
			target() <<getPrintableVar(var(lits.body[i]));
		}
		if(lits.body.size()>1){
			target() <<" -- " <<getPrintableVar(var(lits.body[0])) <<" ";
		}
		target() <<"[color=green];\n";
	}

	void notifyadded(const MinisatID::InnerWLSet& set){
		for(unsigned int i=0; i<set.wls.size(); ++i){
			if(i>0){
				target() <<" -- ";
			}
			target() <<getPrintableVar(var(set.wls[i].getLit()));
		}
		if(set.wls.size()>1){
			target() <<" -- " <<getPrintableVar(var(set.wls[0].getLit())) <<" ";
		}
		target() <<"[color=green];\n";
	}
};

}

#endif /* ECNFGRAPHPARSINGMONITOR_HPP_ */
