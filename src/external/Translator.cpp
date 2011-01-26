/*
 * FODOTTranslator.cpp
 *
 *  Created on: Jan 10, 2011
 *      Author: broes
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

#include <cstring>
#include <cctype>

using namespace std;
using namespace MinisatID;

Translator::Translator(){}

void Translator::printLiteral(std::ostream& output, const Literal& lit) const{
	output <<(lit.hasSign()?"-":"") <<lit.getAtom().getValue() <<"\n";
}

void Translator::printModel(std::ostream& output, const std::vector<Literal>& model){
	bool start = true;
	for (vector<Literal>::const_iterator i = model.begin(); i < model.end(); i++){
		output <<(start ? "" : " ") <<(((*i).hasSign()) ? "-" : "") <<(*i).getAtom().getValue();
		start = false;
	}
	output << " 0\n";
}

void Translator::printHeader(std::ostream& output){
	//Noop
}

FODOTTranslator::FODOTTranslator(bool fodot): Translator(), tofodot(fodot==TRANS_FODOT), modelcounter(0) {

}

FODOTTranslator::~FODOTTranslator() {

}

void FODOTTranslator::addType(string name, const vector<string>& inter){
	type_lookup[name] = types.size();
	types.push_back(inter);
}

void FODOTTranslator::addPred(string name, int num, const vector<string>& ptypes, bool f){
	predicates.push_back(name);
	isfunc.push_back(f);
	int s = 1;
	vector<int> pti;
	for(vector<string>::const_iterator n = ptypes.begin(); n < ptypes.end(); n++) {
		int t = type_lookup[*n];
		pti.push_back(t);
		s = s * types[t].size();
	}
	predtypes.push_back(pti);
	lowestvalue.push_back(num);
	highestvalue.push_back(num + s - 1);
	//cout <<"Predicate/func "  <<*name <<", low=" <<(*num) <<", high=" <<(*num + s -1) <<endl;
}

string FODOTTranslator::getPredName(int predn) const{
	string name = predicates[predn];
	if(!tofodot){
		char first = tolower(name[0]);
		name = name.substr(1);
		name.insert(name.begin(), first);
	}
	return name;
}

void FODOTTranslator::printTuple(const vector<string>& tuple, ostream& output) const{
	bool begin = true;
	for(vector<string>::const_iterator k =tuple.begin(); k < tuple.end(); k++) {
		if(!begin){
			output << ",";
		}
		begin = false;
		output << *k;
	}
}

void FODOTTranslator::printPredicate(int n, const modelvec& model, MODE mode, ostream& output){
	if(predtypes[n].size()==0){
		if(mode != TRANS_ARBIT){
			bool found = false;
			for(vector<string>::const_iterator i=arbitatoms.begin(); !found && i<arbitatoms.end(); i++){
				if((*i).compare(predicates[n])==0){
					found = true;
				}
			}
			if(!found){
				if(tofodot){
					output << getPredName(n);
					if(model[n].size()==0){
						output << " = false\n";
					}else{
						output << " = true\n";
					}
				}else{
					if(model[n].size()!=0){ //Only print if true!
						output << getPredName(n) <<". ";
					}
				}
			}
		}else{
			arbitatoms.push_back(getPredName(n));
		}
		return;
	}

	if(tofodot){
		output << getPredName(n) << " = { ";
	}
	bool tupleseen = false;
	for(vector<vector<string> >::const_iterator m = model[n].begin(); m < model[n].end(); ++m) {
		if(!tofodot){
			output << getPredName(n) << "(";
			printTuple(*m, output);
			output <<"). ";
		}else{
			if(tupleseen){
				output << "; ";
			}
			printTuple(*m, output);
			tupleseen = true;
		}
	}
	if(tofodot){
		output << " }\n";
	}
}

void FODOTTranslator::printFunction(int n, const modelvec& model, ostream& output){
	if(tofodot){
		output << getPredName(n) <<" = ";
		if(predtypes[n].size() == 1) {
			assert(model[n].size()!=0);
			output << model[n][0][0];
			output <<endl;
		}
		else {
			int ts = predtypes[n].size();
			output <<" { ";
			bool tupleseen = false;
			for(vector<vector<string> >::const_iterator m = model[n].begin(); m < model[n].end(); m++) {
				if(tupleseen){
					output << "; ";
				}
				bool begin = true;
				int count = 0;
				for(vector<string>::const_iterator k = (*m).begin(); k < (*m).end(); k++, count++) {
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
		if(predtypes[n].size() == 1) {
			assert(model[n].size()!=0);
			output << getPredName(n) <<"(" << model[n][0][0] <<"). ";
		}
		else {
			for(vector<vector<string> >::const_iterator m = model[n].begin(); m < model[n].end(); ++m) {
				output << getPredName(n) <<"(";
				printTuple(*m, output);
				output <<"). ";
			}
		}
	}
}

void FODOTTranslator::printInterpr(const modelvec& model, MODE mode, ostream& output) {
	for(vector<string>::size_type n = 0; n < predicates.size(); ++n) {
		if(mode!=TRANS_MODEL && model[n].size()==0){
			continue;
		}
		if(isfunc[n]) {
			printFunction(n, model, output);
		} else {
			printPredicate(n, model, mode, output);
		}
	}
}

//IMPORTANT: non-incremental (slow), so do not use for printing a full model!
void FODOTTranslator::printLiteral(std::ostream& output, const Literal& lit) const {
	uint pred = 0;
	vector<string> args;
	deriveStringFromAtomNumber(lit.getAtom().getValue(), pred, args);

	if(isfunc[pred]) {
		output <<(lit.hasSign()?"~":"");
		bool begin = true;
		if(args.size()>1){
			output << "(";
		}
		for(uint k=0; k<args.size()-1; k++) {
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
		output <<(lit.hasSign()?"~":"") << getPredName(pred) << "(";
		printTuple(args, output);
		output <<")\n";
	}
}

void FODOTTranslator::printModel(std::ostream& output, const vector<Literal>& model) {
	if(tofodot){
		output << "=== Model " << ++modelcounter << " ===\n";
	}

	// set initial values
	uint currpred = 0;

	modelvec temptruemodelcombined = truemodelcombinedout;

	// read and translate the model
	bool endmodel = false;
	for(vector<Literal>::const_iterator i=model.begin(); i<model.end(); i++){
		int lit = (*i).getValue();
		if(lit==0 || endmodel){ //end of model found
			break;
		}else if(lit<0){
			continue;
		}else if(lit > largestnottseitinatom){
			endmodel = true;
		}else{
			vector<string> arg;
			if(deriveStringFromAtomNumber(lit, currpred, arg)){
				truemodelcombinedout[currpred].push_back(arg);
			}
		}
	}
	printInterpr(truemodelcombinedout, TRANS_MODEL, output);
	output <<"\n";
}


/**
 * IMPORTANT: it IS possible that the number is not within the range of ANY symbol that should
 * be translated (even if it is not larger than the largest one)!
 * @pre: atom is NOT larger than the largest relevant (not tseitin) number.
 * @pre: atom is positive
 */
bool FODOTTranslator::deriveStringFromAtomNumber(int atom, uint& currpred, vector<string>& arg) const{
	//output <<"Translating " <<atom <<endl;
	while(atom > highestvalue[currpred]) {
		currpred++;
	}
	if(atom < lowestvalue[currpred]){
		return false;
	}

	int valueleft = atom;
	assert(currpred < predicates.size());
	valueleft = atom - lowestvalue[currpred];
	for(int n = predtypes[currpred].size() - 1; n >= 0 ; n--) {
		int cs = types[predtypes[currpred][n]].size();
		int carg = valueleft % cs;
		arg.push_back(types[predtypes[currpred][n]][carg]);
		valueleft = (valueleft - carg) / cs;
	}
	std::reverse(arg.begin(), arg.end());

	return true;
}

void FODOTTranslator::printHeader(ostream& output){
	largestnottseitinatom = highestvalue[predicates.size()-1];
	trueout = modelvec(predicates.size());
	arbitout = modelvec(predicates.size());
	truemodelcombinedout = modelvec(predicates.size());

	if(predicates.empty()) return;

	// set initial values
	uint	currpred = 0;

	// read and translate the model
	int curr;
	for(vector<int>::const_iterator m=truelist.begin(); m<truelist.end(); m++) {
		curr = *m;
		if(curr > largestnottseitinatom){
			return;
		}else{
			vector<string> arg;
			if(deriveStringFromAtomNumber(curr, currpred, arg)){
				trueout[currpred].push_back(arg);
				truemodelcombinedout[currpred].push_back(arg);
			}
		}
	}

	// set initial values
	currpred = 0;

	// read and translate the model
	for(vector<int>::const_iterator m=arbitlist.begin(); m<arbitlist.end(); m++) {
		curr = *m;
		if(curr > largestnottseitinatom){
			return;
		}else{
			vector<string> arg;
			if(deriveStringFromAtomNumber(curr, currpred, arg)){
				arbitout[currpred].push_back(arg);
			}
		}
	}

	if(predicates.empty()) return;

	if(tofodot){
		if(truelist.size()>0){
				output << "=== Certainly true atoms (also added to each model) ===\n";
			printInterpr(trueout, TRANS_TRUE, output);
			output <<"\n";
		}
		if(arbitlist.size()>0){
			output << "=== Atoms with arbitrary truth value (not shown in models!) ===\n";
			printInterpr(arbitout, TRANS_ARBIT, output);
			output <<"\n";
		}
	}
}

void LParseTranslator::addTuple(Atom atom, std::string name) {
	lit2name[atom]=name;
}

void LParseTranslator::printModel(std::ostream& output, const std::vector<Literal>& model) {
	for(vector<Literal>::const_iterator i=model.begin(); i<model.end(); i++){
		if(!(*i).hasSign()){ //Do not print false literals
			map<Atom, string>::const_iterator it = lit2name.find((*i).getAtom());
			if(it!=lit2name.end()){
				output <<(*it).second <<" ";
			}
		}
	}
	output <<"\n";
}

void LParseTranslator::printLiteral(std::ostream& output, const Literal& lit) const {
	map<Atom, string>::const_iterator it = lit2name.find(lit.getAtom());
	if(it!=lit2name.end()){
		output <<(lit.hasSign()?"~":"") <<(*it).second <<"\n";
	}
}

void LParseTranslator::printHeader(std::ostream& output) {

}
