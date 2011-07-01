/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#include "external/Translator.hpp"

#include <string>
#include <vector>
#include <fstream>
#include <iostream>
#include <sstream>
#include <assert.h>
#include <algorithm>

#include <GeneralUtils.hpp>
#include <utils/Print.hpp>

#include <external/SolvingMonitor.hpp>

using namespace std;
using namespace MinisatID;

// REENTRANT
void FODOTTranslator::finishData(){
	if(finisheddata){
		return;
	}
	finisheddata = true;
	if(emptytrans){
		return;
	}

	largestnottseitinatom = symbols.back()->endnumber;

	for(std::vector<Symbol*>::const_iterator i=symbols.begin(); i<symbols.end(); ++i){
		truemodelcombinedout.push_back(SymbolInterpr(*i));
		symbolasarbitatomlist[*i]=false;
	}

	// parse the certainly true atoms
	for(std::vector<int>::const_iterator m=truelist.begin(); m<truelist.end(); ++m) {
		int curr = *m;
		if(curr > largestnottseitinatom){
			continue;
		}else{
			AtomInfo info = deriveStringFromAtomNumber(curr);
			if(info.hastranslation){
				truemodelcombinedout[info.symbolindex].tuples.push_back(TupleInterpr(FIXED_TRUE, info.arg));
			}
		}
	}
}

// REENTRANT
void FODOTTranslator::finishParsing(ostream& output){
	if(emptytrans){
		return;
	}
	finishData();
	if(!printedArbitrary){
		int modelsRepresentedByArbitrary= 0;
		for(std::vector<int>::const_iterator m=arbitlist.begin(); m<arbitlist.end(); ++m) {
			int curr = *m;
			if(curr > largestnottseitinatom){
				continue;
			}else{
				AtomInfo info = deriveStringFromAtomNumber(curr);
				if(info.hastranslation){
					Symbol* symbol = symbols[info.symbolindex];
					SymbolInterpr interpr(symbol);
					interpr.tuples.push_back(TupleInterpr(FIXED_ARBIT, info.arg));
					arbitout.push_back(interpr);
					++modelsRepresentedByArbitrary;
					if(symbol->types.size()==0){ //atom
						symbolasarbitatomlist[symbol] = true;
					}
				}
			}
		}
		if(modelsRepresentedByArbitrary>0){
			if(tofodot){
				output <<"Arbitrary truth values (representing 2^" <<modelsRepresentedByArbitrary <<" interpretations):\n";
				printInterpr(arbitout, output, PRINT_ARBIT);
			}else{
				output <<"Arbitrary truth values represent 2^" <<modelsRepresentedByArbitrary <<" interpretations.\n";
			}
		}

		printedArbitrary = true;
	}
}

void FODOTTranslator::printPredicate(const SymbolInterpr& pred, ostream& output, PRINTCHOICE print) const {
	assert(!pred.symbol->isfunction);

	if(pred.symbol->types.size()==0){ //ATOM
		bool arbitrary = symbolasarbitatomlist.at(pred.symbol);
		if(print==PRINT_ARBIT && arbitrary){
			output <<pred.symbol->getName(tofodot) <<"\n";
		}else if(print!=PRINT_ARBIT && !arbitrary){

			bool atomtrue = pred.tuples.size()!=0;
			if(tofodot){
				output <<pred.symbol->getName(tofodot);
				if(!atomtrue){
					output << " = false\n";
				}else{ //True
					output << " = true\n";
				}
			}else if(atomtrue){ //asp && true
				output <<pred.symbol->getName(tofodot) <<". ";
			}
		}
	}else{
		if(tofodot){
			output << pred.symbol->getName(tofodot) << " = { ";
		}
		bool tupleseen = false;
		for(vector<TupleInterpr>::const_iterator m = pred.tuples.begin(); m < pred.tuples.end(); ++m) {
			if(!tofodot){
				output << pred.symbol->getName(tofodot) << "(";
				printTuple((*m).arguments, output);
				output <<"). ";
			}else{
				if(tupleseen){
					output << "; ";
				}
				printTuple((*m).arguments, output);
				tupleseen = true;
			}
		}
		if(tofodot){
			output << " }\n";
		}
	}
}

void FODOTTranslator::printFunction(const SymbolInterpr& func, ostream& output, PRINTCHOICE print) const{
	if(tofodot){
		output <<func.symbol->getName(tofodot) <<" = ";
		if(func.symbol->types.size() == 1) {
			assert(func.tuples.size()==1);
			output << func.tuples.back().arguments[0] <<"\n";
		} else {
			int ts = func.symbol->types.size();
			output <<" { ";
			bool tupleseen = false;
			for(vector<TupleInterpr>::const_iterator m = func.tuples.begin(); m < func.tuples.end(); ++m) {
				if(tupleseen){
					output << "; ";
				}
				bool begin = true;
				int count = 0;
				for(vector<string>::const_iterator k = (*m).arguments.begin(); k < (*m).arguments.end(); ++k, ++count) {
					if(!begin){
						output << (count==ts-1?"->":",");
					}
					begin = false;
					output << (*k);
				}
				tupleseen = true;
			}
			output << " }\n";
		}
	}else{
		if(func.symbol->types.size() == 1) {
			assert(func.tuples.size()!=0);
			output << func.symbol->getName(tofodot) <<"(" << func.tuples[0].arguments[0] <<"). ";
		}
		else {
			for(vector<TupleInterpr>::const_iterator m = func.tuples.begin(); m < func.tuples.end(); ++m) {
				output << func.symbol->getName(tofodot) <<"(";
				printTuple((*m).arguments, output);
				output <<"). ";
			}
		}
	}
}

void FODOTTranslator::printInterpr(const modelvec& model, ostream& output, PRINTCHOICE printfixed) const{
	for(vector<SymbolInterpr>::const_iterator n = model.begin(); n < model.end(); ++n) {
		if((*n).symbol->isfunction) {
			printFunction(*n, output, printfixed);
		} else {
			printPredicate(*n, output, printfixed);
		}
	}
	if(!tofodot){
		output <<"\n";
	}
	output.flush();
}

//IMPORTANT: non-incremental (slow), so do not use for printing a full model!
void FODOTTranslator::printLiteral(std::ostream& output, const Literal& lit) {
	if(!finisheddata){
		finishParsing(output);
	}

	if(emptytrans){
		return;
	}

	AtomInfo info = deriveStringFromAtomNumber(lit.getAtom().getValue());
	if(!info.hastranslation){
		return;
	}

	if(symbols[info.symbolindex]->isfunction) {
		output <<(lit.hasSign()?"~":"");
		bool begin = true;
		if(info.arg.size()>1){
			output << "(";
		}
		for(uint k=0; k<info.arg.size()-1; ++k) {
			if(!begin){
				output << ",";
			}
			begin = false;
			output << info.arg[k];
		}
		if(info.arg.size()>1){
			output << ")";
		}
		output <<info.arg.back()<<"\n";
	} else {
		output <<(lit.hasSign()?"~":"") << symbols[info.symbolindex]->getName(tofodot) << "(";
		printTuple(info.arg, output);
		output <<")\n";
	}
}

void FODOTTranslator::printModel(std::ostream& output, const Model& model) {
	if(!finisheddata){
		finishParsing(output);
	}

	if(emptytrans){
		return;
	}

	modelvec temptruemodelcombined = truemodelcombinedout;

	// read and translate the model
	bool endmodel = false;
	for(vector<Literal>::const_iterator i=model.literalinterpretations.begin(); i<model.literalinterpretations.end(); ++i){
		int lit = (*i).getValue();
		if(lit==0 || endmodel){ //end of model found
			break;
		}else if(lit<0){ //Only print true literals
			continue;
		}else if(lit > largestnottseitinatom){
			endmodel = true;
		}else{
			AtomInfo info = deriveStringFromAtomNumber(lit);
			if(info.hastranslation){
				temptruemodelcombined[info.symbolindex].tuples.push_back(TupleInterpr(FIXED_TRUE, info.arg));
			}
		}
	}
	if(tofodot){
		output <<"Model:\n";
	}
	printInterpr(temptruemodelcombined, output, PRINT_FIXED);
	assert(model.variableassignments.size()==0);
}


/**
 * IMPORTANT: it IS possible that the number is not within the range of ANY symbol that should
 * be translated (even if it is not larger than the largest one)!
 * @pre: atom is NOT larger than the largest relevant (not tseitin) number.
 * @pre: atom is positive
 */
FODOTTranslator::AtomInfo FODOTTranslator::deriveStringFromAtomNumber(int atom) const{
	AtomInfo info;
	info.symbolindex = 0;

	uint& index = info.symbolindex;
	while(atom > symbols[index]->endnumber) {
		++index;
	}
	if(atom < symbols[index]->startnumber){
		info.hastranslation = false;
		return info;
	}

	int valueleft = atom;
	assert(index < symbols.size());
	valueleft = atom-symbols[index]->startnumber;
	for(vector<Type*>::const_reverse_iterator n=symbols[index]->types.rbegin(); n < symbols[index]->types.rend(); ++n) {
		int cs = (*n)->domainelements.size();
		int carg = valueleft % cs;
		string domelem = (*n)->domainelements[carg];
		if(!tofodot){
			char first = tolower(domelem[0]);
			domelem = domelem.substr(1);
			domelem.insert(domelem.begin(), first);
		}
		info.arg.push_back(domelem);
		valueleft = (valueleft - carg) / cs;
	}
	std::reverse(info.arg.begin(), info.arg.end());

	info.hastranslation = true;
	return info;
}
