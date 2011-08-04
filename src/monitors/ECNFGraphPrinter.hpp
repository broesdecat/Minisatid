/*
 * HumanReadableParsingMonitor.hpp
 *
 *  Created on: 26-mei-2011
 *      Author: Broes
 */

#ifndef HUMANREADABLEPARSINGMONITOR_HPP_
#define HUMANREADABLEPARSINGMONITOR_HPP_

#include "monitors/ParsingMonitor.hpp"

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
		for(int i=0; i<lits.literals.size(); ++i){
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
		for(int i=0; i<lits.body.size(); ++i){
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

	void notifyadded(const MinisatID::InnerSet& lits){
		for(unsigned int i=0; i<lits.literals.size(); ++i){
			if(i>0){
				target() <<" -- ";
			}
			target() <<getPrintableVar(var(lits.literals[i]));
		}
		if(lits.literals.size()>1){
			target() <<" -- " <<getPrintableVar(var(lits.literals[0])) <<" ";
		}
		target() <<"[color=green];\n";
	}

	void notifyadded(const MinisatID::InnerWSet& lits){
		for(unsigned int i=0; i<lits.literals.size(); ++i){
			if(i>0){
				target() <<" -- ";
			}
			target() <<getPrintableVar(var(lits.literals[i]));
		}
		if(lits.literals.size()>1){
			target() <<" -- " <<getPrintableVar(var(lits.literals[0])) <<" ";
		}
		target() <<"[color=green];\n";
	}
};

}

#endif /* HUMANREADABLEPARSINGMONITOR_HPP_ */
