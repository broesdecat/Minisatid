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

#include <string>
#include <iostream>
#include <algorithm>

#include <GeneralUtils.hpp>
#include <utils/Print.hpp>

#include <external/SolvingMonitor.hpp>

using namespace std;
using namespace MinisatID;

Translator::Translator(): modelcounter(0){}

void Translator::printLiteral(std::ostream& output, const Literal& lit){
	output <<(lit.hasSign()?"-":"") <<lit.getAtom().getValue() <<"\n";
}

void Translator::printCurrentOptimum(std::ostream& output, const Weight& value){

}

void Translator::printModel(std::ostream& output, const Model& model){
	stringstream ss;
	for (vector<Literal>::const_iterator i = model.literalinterpretations.begin(); i < model.literalinterpretations.end(); ++i){
		ss <<(((*i).hasSign()) ? "-" : "") <<(*i).getAtom().getValue() <<" ";
	}
	for (vector<VariableEqValue>::const_iterator i = model.variableassignments.begin(); i < model.variableassignments.end(); ++i){
		ss <<(*i).variable <<"=" <<(*i).value <<" ";
	}
	ss << "0\n";
	//TODO start critical section
	output <<ss.str();
	// end critical section
	output.flush();
}

void Translator::printHeader(std::ostream& output){
	//Noop
}


std::string Symbol::getName(bool fodot){
	if(fodot){
		return name;
	}else{
		string n = name;
		n.at(0)=tolower(n.at(0));
		return n;
	}
}

FODOTTranslator::FODOTTranslator(OUTPUTFORMAT fodot): Translator(),
		tofodot(fodot==TRANS_FODOT), finisheddata(false), emptytrans(true) {
	assert(fodot!=TRANS_PLAIN);
}

FODOTTranslator::~FODOTTranslator() {
	deleteList<Type>(types);
	deleteList<Symbol>(symbols);
}

void FODOTTranslator::addType(string name, const vector<string>& inter){
	types.insert(pair<string,Type*>(name, new Type(name, inter)));
}

void FODOTTranslator::addPred(string name, int startingnumber, const vector<string>& typenames, bool isfunction){
	vector<Type*> argtypes;
	int joinsize = 1;
	for(vector<string>::const_iterator i = typenames.begin(); i < typenames.end(); ++i) {
		argtypes.push_back(types.at(*i));
		joinsize *= argtypes.back()->domainelements.size();
	}

	symbols.push_back(new Symbol(name, startingnumber, startingnumber+joinsize-1, argtypes, isfunction));
	emptytrans = false;
}

void FODOTTranslator::finishParsing(ostream& output){
	finisheddata = true;

	if(emptytrans){
		return;
	}

	largestnottseitinatom = symbols.back()->endnumber;

	for(vector<Symbol*>::const_iterator i=symbols.begin(); i<symbols.end(); ++i){
		arbitout.push_back(SymbolInterpr(*i));
		truemodelcombinedout.push_back(SymbolInterpr(*i));
		symbolasarbitatomlist[*i]=false;
	}

	// set initial values
	uint currpred = 0;
	// parse the certainly true atoms
	int curr;
	for(vector<int>::const_iterator m=truelist.begin(); m<truelist.end(); ++m) {
		curr = *m;
		if(curr > largestnottseitinatom){
			return;
		}else{
			vector<string> arg;
			if(deriveStringFromAtomNumber(curr, currpred, arg)){
				truemodelcombinedout[currpred].tuples.push_back(TupleInterpr(FIXED_TRUE, arg));
			}
		}
	}

	// set initial values
	currpred = 0;

	// parse and print the arbitrary literals
	bool hasarbitraries = false;
	double nbofmodels = 0;
	for(vector<int>::const_iterator m=arbitlist.begin(); m<arbitlist.end(); ++m) {
		curr = *m;
		if(curr > largestnottseitinatom){
			return;
		}else{
			vector<string> arg;
			if(deriveStringFromAtomNumber(curr, currpred, arg)){
				arbitout[currpred].tuples.push_back(TupleInterpr(FIXED_ARBIT, arg));
				++nbofmodels;
				hasarbitraries = true;
				if(arbitout[currpred].symbol->types.size()==0){ //atom
					symbolasarbitatomlist[symbols[currpred]] = true;
				}
			}
		}
	}
	if(hasarbitraries){
		if(tofodot){
			output <<"Arbitrary truth values (representing 2^" <<nbofmodels <<" interpretations):\n";
			printInterpr(arbitout, output, PRINT_ARBIT);
		}else{
			clog <<"Arbitrary truth values represent 2^" <<nbofmodels <<" interpretations.\n";
		}
	}
}

void FODOTTranslator::printTuple(const vector<string>& tuple, ostream& output) const{
	bool begin = true;
	for(vector<string>::const_iterator k = tuple.begin(); k < tuple.end(); ++k) {
		if(!begin){
			output << ",";
		}
		begin = false;
		output << *k;
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

	uint pred = 0;
	vector<string> args;
	deriveStringFromAtomNumber(lit.getAtom().getValue(), pred, args);

	if(symbols[pred]->isfunction) {
		output <<(lit.hasSign()?"~":"");
		bool begin = true;
		if(args.size()>1){
			output << "(";
		}
		for(uint k=0; k<args.size()-1; ++k) {
			if(!begin){
				output << ",";
			}
			begin = false;
			output << args[k];
		}
		if(args.size()>1){
			output << ")";
		}
		output <<args.back()<<"\n";
	} else {
		output <<(lit.hasSign()?"~":"") << symbols[pred]->getName(tofodot) << "(";
		printTuple(args, output);
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

	// set initial values
	uint currpred = 0;

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
			vector<string> arg;
			if(deriveStringFromAtomNumber(lit, currpred, arg)){
				temptruemodelcombined[currpred].tuples.push_back(TupleInterpr(FIXED_TRUE, arg));
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
bool FODOTTranslator::deriveStringFromAtomNumber(int atom, uint& currpred, vector<string>& arg) const{
	while(atom > symbols[currpred]->endnumber) {
		++currpred;
	}
	if(atom < symbols[currpred]->startnumber){
		return false;
	}

	int valueleft = atom;
	assert(currpred < symbols.size());
	valueleft = atom-symbols[currpred]->startnumber;
	for(vector<Type*>::const_reverse_iterator n=symbols[currpred]->types.rbegin(); n < symbols[currpred]->types.rend(); ++n) {
		int cs = (*n)->domainelements.size();
		int carg = valueleft % cs;
		string domelem = (*n)->domainelements[carg];
		if(!tofodot){
			char first = tolower(domelem[0]);
			domelem = domelem.substr(1);
			domelem.insert(domelem.begin(), first);
		}
		arg.push_back(domelem);
		valueleft = (valueleft - carg) / cs;
	}
	std::reverse(arg.begin(), arg.end());

	return true;
}

void FODOTTranslator::printHeader(ostream& output){
	if(!finisheddata){
		finishParsing(output);
	}

	if(emptytrans){
		return;
	}
}



void LParseTranslator::addTuple(Atom atom, std::string name) {
	lit2name[atom]=name;
}

void LParseTranslator::printModel(std::ostream& output, const Model& model) {
	for(vector<Literal>::const_iterator i=model.literalinterpretations.begin(); i<model.literalinterpretations.end(); ++i){
		if(!(*i).hasSign()){ //Do not print false literals
			map<Atom, string>::const_iterator it = lit2name.find((*i).getAtom());
			if(it!=lit2name.end()){
				output <<(*it).second <<" ";
			}
		}
	}
	output <<"\n";
	output.flush();
	assert(model.variableassignments.size()==0);
}

void LParseTranslator::printLiteral(std::ostream& output, const Literal& lit) {
	map<Atom, string>::const_iterator it = lit2name.find(lit.getAtom());
	if(it!=lit2name.end()){
		output <<(lit.hasSign()?"~":"") <<(*it).second <<"\n";
	}
}
void LParseTranslator::printHeader(std::ostream& output) {

}

void OPBTranslator::addTuple(Atom atom, std::string name) {
	lit2name[atom]=name;
}

void OPBTranslator::printModel(std::ostream& output, const Model& model) {
	output <<"v ";
	for(vector<Literal>::const_iterator i=model.literalinterpretations.begin(); i<model.literalinterpretations.end(); ++i){
		map<Atom, string>::const_iterator it = lit2name.find((*i).getAtom());
		if(it!=lit2name.end()){
			if((*i).hasSign()){
				output <<"-";
			}
			output <<(*it).second <<" ";
		}
	}
	output <<"\n";
	output.flush();
	assert(model.variableassignments.size()==0);
}

void OPBTranslator::printLiteral(std::ostream& output, const Literal& lit) {

}

void OPBTranslator::printCurrentOptimum(std::ostream& output, const Weight& value){
	output <<"o " <<value <<"\n";
}

void OPBTranslator::printHeader(std::ostream& output) {

}
