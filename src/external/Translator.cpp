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

FODOTTranslator::FODOTTranslator(bool fodot): Translator(), tofodot(fodot), modelcounter(0) {

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

string FODOTTranslator::getPredName(int predn){
	string name = predicates[predn];
	if(!tofodot){
		char first = tolower(name[0]);
		name = name.substr(1);
		name.insert(name.begin(), first);
	}
	return name;
}

void FODOTTranslator::printTuple(const vector<string>& tuple, ostream& output){
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
						output << getPredName(n) <<".\n";
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
			output <<").\n";
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
			output << getPredName(n) <<"(" << model[n][0][0] <<").\n";
		}
		else {
			for(vector<vector<string> >::const_iterator m = model[n].begin(); m < model[n].end(); ++m) {
				output << getPredName(n) <<"(";
				printTuple(*m, output);
				output <<").\n";
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

void FODOTTranslator::printModel(std::ostream& output, const vector<int>& model){
	if(tofodot){
		output << "=== Model " << ++modelcounter << " ===\n";
	}

	// set initial values
	int	currpred = 0;

	modelvec tempmodel, temptruemodelcombined;
	tempmodel = modelout;
	temptruemodelcombined = truemodelcombinedout;

	// read and translate the model
	int curr;
	bool endmodel = false;
	for(auto i=model.begin(); i<model.end(); i++){
		curr = *i;
		if(curr==0 || endmodel){ //end of model found
			break;
		}else if(curr<0){
			continue;
		}else if(curr > largestnottseitinatom){
			endmodel = true;
		}else{
			vector<string> arg;
			if(deriveStringFromAtomNumber(curr, currpred, arg)){
				modelout[currpred].push_back(arg);
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
bool FODOTTranslator::deriveStringFromAtomNumber(int atom, int& currpred, vector<string>& arg){
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

void FODOTTranslator::printHeader(ostream& output) {
	largestnottseitinatom = highestvalue[predicates.size()-1];
	trueout = modelvec(predicates.size());
	arbitout = modelvec(predicates.size());
	modelout = modelvec(predicates.size());
	truemodelcombinedout = modelvec(predicates.size());

	if(predicates.empty()) return;

	// set initial values
	int	currpred = 0;

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

void LParseTranslator::addTuple(int lit, std::string name) { lit2name[lit]=name; }

void LParseTranslator::printModel(std::ostream& output, const std::vector<int>& model){
	for(auto i=model.begin(); i<model.end(); i++){
		if((*i)>0){
			auto it = lit2name.find(*i);
			if(it!=lit2name.end()){
				output <<lit2name[(*i)] <<"\n";
			}
		}
	}
}

void LParseTranslator::printHeader(std::ostream& output){

}
