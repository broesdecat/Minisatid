//--------------------------------------------------------------------------------------------------
//    Copyright (c) 2009-2010, Broes De Cat, K.U.Leuven, Belgium
//    
//    Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
//    associated documentation files (the "Software"), to deal in the Software without restriction,
//    including without limitation the rights to use, copy, modify, merge, publish, distribute,
//    sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
//    furnished to do so, subject to the following conditions:
//    
//    The above copyright notice and this permission notice shall be included in all copies or
//    substantial portions of the Software.
//    
//    THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
//    NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
//    NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
//    DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
//    OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
//--------------------------------------------------------------------------------------------------

// Copyright 1998 by Patrik Simons
// This program is free software; you can redistribute it and/or
// modify it under the terms of the GNU General Public License
// as published by the Free Software Foundation; either version 2
// of the License, or (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program; if not, write to the Free Software
// Foundation, Inc., 59 Temple Place - Suite 330, Boston,
// MA 02111-1307, USA.
//
// Patrik.Simons@hut.fi
#include <iostream>
#include <float.h>
#include <limits.h>
#include <string.h>

#include "parser/Lparseread.hpp"
#include "external/Translator.hpp"

using namespace std;
using namespace MinisatID;

typedef enum {
	ENDRULE = 0, BASICRULE = 1, CONSTRAINTRULE = 2, CHOICERULE = 3,
	GENERATERULE = 4, WEIGHTRULE = 5, OPTIMIZERULE = 6
} RuleType;

Read::Read(WrappedPCSolver* solver) :
		endedparsing(false),
		maxatomnumber(1), setcount(1), size(0),
		solver(solver), optim(false),
		translator(new LParseTranslator()){
	solver->setTranslator(translator);
}

Read::~Read() {
	deleteList<BasicRule>	(basicrules);
	deleteList<SumRule>		(sumrules);
	deleteList<CardRule>	(cardrules);
	deleteList<ChoiceRule>	(choicerules);
}

Atom Read::makeParsedAtom(int n){
	Atom atom = makeAtom(n);
	pair<Atom, bool> p(atom,true);
	defatoms.insert(p);
	return atom;
}

Atom Read::makeNewAtom(){
	assert(endedparsing);
	return makeAtom(++maxatomnumber);
}

Atom Read::makeAtom(int n){
	if (maxatomnumber < n) {
		maxatomnumber = n;
	}
	getSolver()->addVar(Atom(n));
	return Atom(n);
}

bool Read::readBody(istream &f, long size, bool pos, vector<Literal>& body) {
	long n;
	for (long i = 0; i < size; i++) {
		f >> n;
		if (!f.good() || n < 1) {
			char s[100];
			sprintf(s, "atom out of bounds, line %ld\n", linenumber);
			throw idpexception(s);
		}
		body.push_back(Literal(makeParsedAtom(n), !pos));
	}
	return true;
}

bool Read::readFullBody(istream &f, vector<Literal>& body){
	long n;
	f >> n; // total body size
	if (!f.good() || n < 0) {
		char s[100];
		sprintf(s, "total body size, line %ld\n", linenumber);
		throw idpexception(s);
	}
	long bodysize = n;

	f >> n; // size of negative body
	if (!f.good() || n < 0 || n > bodysize) {
		char s[100];
		sprintf(s, "negative body size, line %ld\n", linenumber);
		throw idpexception(s);
	}
	long negbodysize = n;

	if (!readBody(f, negbodysize, false, body)) { // Negative body: negated literals
		return false;
	}
	if (!readBody(f, bodysize - negbodysize, true, body)) { // Positive body
		return false;
	}
	return true;
}

bool Read::readWeights(std::istream &f, std::vector<Weight>& weights, int bodysize){
	Weight sum = 0, w = 0;
	for (long i = 0; i < bodysize; i++) {
		f >> w;
		if (!f.good()) {
			return false;
		}
		if ((w>0 && posInfinity()-w<sum) || (w<0 && negInfinity()-w>sum)) {
			char s[100];
			sprintf(s, "sum of weights in weight rule too large or too small, line %ld\n", linenumber);
			throw idpexception(s);
		}
		sum += w;
		weights.push_back(w);
	}
	return true;
}

bool Read::parseBasicRule(istream &f) {
	long n;
	f >> n; // rule head
	if (!f.good() || n < 1) {
		char s[100];
		sprintf(s, "head atom out of bounds, line %ld\n", linenumber);
		throw idpexception(s);
	}
	Atom head = makeParsedAtom(n);

	vector<Literal> body;
	if(!readFullBody(f, body)){
		return false;
	}

	basicrules.push_back(new BasicRule(Literal(head), body));
	return true;
}

bool Read::parseConstraintRule(istream &f) {
	long n;
	f >> n; // rule head
	if (!f.good() || n < 1) {
		char s[100];
		sprintf(s, "head atom out of bounds, line %ld\n", linenumber);
		throw idpexception(s);
	}
	Atom head = makeParsedAtom(n);

	f >> n; // total body size
	if (!f.good() || n < 0) {
		char s[100];
		sprintf(s, "total body size, line %ld\n", linenumber);
		throw idpexception(s);
	}
	long bodysize = n;

	f >> n; // size of negative body
	if (!f.good() || n < 0 || n > bodysize) {
		char s[100];
		sprintf(s, "negative body size, line %ld\n", linenumber);
		throw idpexception(s);
	}
	long negbodysize = n;

	f >> n; //at least n body atoms have to be true
	if (!f.good() || n < 0 || n > bodysize) {
		return false;
	}
	long atleast = n;

	vector<Literal> body;
	if (!readBody(f, negbodysize, false, body)) { // Negative body: negated literals
		return false;
	}
	if (!readBody(f, bodysize - negbodysize, true, body)) { // Positive body
		return false;
	}

	cardrules.push_back(new CardRule(setcount++, Literal(head), body, Weight(atleast)));
	return true;
}

bool Read::parseChoiceRule(istream &f) {
	long n;

	f >> n; // number of heads
	if (!f.good() || n < 1) {
		char s[100];
		sprintf(s, "head size less than one, line %ld\n", linenumber);
		throw idpexception(s);
	}
	long headssize = n;

	vector<Literal> heads;
	for (long i = 0; i < headssize; i++) {
		f >> n;
		if (!f.good() || n < 1) {
			char s[100];
			sprintf(s, "atom out of bounds, line %ld\n", linenumber);
			throw idpexception(s);
		}
		heads.push_back(Literal(makeParsedAtom(n)));
	}

	vector<Literal> body;
	if(!readFullBody(f, body)){
		return false;
	}

	choicerules.push_back(new ChoiceRule(heads, body));
	return true;
}

bool Read::parseWeightRule(istream &f) {
	long n;
	f >> n; // number of heads
	if (!f.good() || n < 1) {
		char s[100];
		sprintf(s, "head atom out of bounds, line %ld\n", linenumber);
		throw idpexception(s);
	}
	Atom head = makeParsedAtom(n);

	Weight lowerbound;
	f >> lowerbound; // lower bound of the sum
	if (!f.good()) {
		return false;
	}

	vector<Literal> body;
	if(!readFullBody(f, body)){
		return false;
	}

	vector<Weight> weights;
	if(!readWeights(f, weights, body.size())){
		return false;
	}

	sumrules.push_back(new SumRule(setcount++, Literal(head), body, weights, lowerbound));
	return true;
}

bool Read::parseOptimizeRule(istream &f) {
	long n;
	f >> n; // formerly choice between min or max, only 0 (minimize) still accepted
	if (!f.good())
		return false;
	if(n!=0){
		char s[100];
		sprintf(s, "maximize statements are no longer accepted, line %ld\n", linenumber);
		throw idpexception(s);
	}

	vector<Literal> body;
	if(!readFullBody(f, body)){
		return false;
	}

	//Weights
	vector<Weight> weights;
	if(!readWeights(f, weights, body.size())){
		return false;
	}

	optim = true;
	optimbody = body;
	optimweights = weights;
	optimsetcount = setcount++;
	return true;
}

bool Read::addBasicRules() {
	for (vector<BasicRule*>::const_iterator i = basicrules.begin(); i < basicrules.end(); i++) {
		if (!getSolver()->addRule((*i)->conj, (*i)->head, (*i)->body)) {
			return false;
		}
	}
	return true;
}

bool Read::addCardRules() {
	for (vector<CardRule*>::const_iterator i = cardrules.begin(); i < cardrules.end(); i++) {
		if (!getSolver()->addSet((*i)->setcount, (*i)->body)) {
			return false;
		}
		if (!getSolver()->addAggrExpr((*i)->head, (*i)->setcount, (*i)->atleast, AGGSIGN_LB, CARD, DEF)) {
			return false;
		}
	}
	return true;
}

bool Read::addSumRules() {
	for (vector<SumRule*>::const_iterator i = sumrules.begin(); i < sumrules.end(); i++) {
		if (!getSolver()->addSet((*i)->setcount, (*i)->body, (*i)->weights)) {
			return false;
		}
		if (!getSolver()->addAggrExpr((*i)->head, (*i)->setcount, (*i)->atleast, AGGSIGN_LB, SUM, DEF)) {
			return false;
		}
	}
	return true;
}

void Read::addRuleToHead(map<Atom, vector<BasicRule*> >& headtorules, BasicRule* rule, Atom head){
	if (headtorules.find(head) == headtorules.end()) {
		headtorules.insert(pair<Atom, vector<BasicRule*> > (head, std::vector<BasicRule*>()));
	}
	(*headtorules.find(head)).second.push_back(rule);
}

bool Read::tseitinizeHeads(){
	// Transform away all choicerules
	for (vector<ChoiceRule*>::const_iterator i = choicerules.begin(); i < choicerules.end(); i++) {
		vector<Literal> tempbody;
		tempbody.push_back(Literal(1)); //reserve space for the extra choice literal
		tempbody.insert(tempbody.end(), (*i)->body.begin(), (*i)->body.end());
		for (vector<Literal>::const_iterator j = (*i)->heads.begin(); j < (*i)->heads.end(); j++) {
			const Literal& head = *j;
			tempbody[0] = Literal(makeNewAtom());
			basicrules.push_back(new BasicRule(head, tempbody));

			//To guarantee #model equivalence:
			vector<Literal> lits;
			lits.push_back(head);
			if(!getSolver()->addEquivalence(tempbody[0], lits, true)){
				return false;
			}
		}
	}

	//Check whether there are multiple occurrences and rewrite them using tseitin!
	map<Atom, vector<BasicRule*> > headtorules;
	for (vector<BasicRule*>::const_iterator i = basicrules.begin(); i < basicrules.end(); i++) {
		addRuleToHead(headtorules, *i, (*i)->head.getAtom());
	}
	for (vector<CardRule*>::const_iterator i = cardrules.begin(); i < cardrules.end(); i++) {
		addRuleToHead(headtorules, *i, (*i)->head.getAtom());
	}
	for (vector<SumRule*>::const_iterator i = sumrules.begin(); i < sumrules.end(); i++) {
		addRuleToHead(headtorules, *i, (*i)->head.getAtom());
	}

	//Tseitinize
	for (map<Atom, vector<BasicRule*> >::const_iterator i = headtorules.begin(); i != headtorules.end(); i++) {
		if ((*i).second.size() < 2) { //No multiple heads
			continue;
		}

		vector<Literal> newheads;
		for (vector<BasicRule*>::const_iterator j = (*i).second.begin(); j < (*i).second.end(); j++) {
			Literal newhead = Literal(makeNewAtom());
			newheads.push_back(newhead);
			(*j)->head = newhead;
		}
		basicrules.push_back(new BasicRule(Literal((*i).first), newheads, false));
	}

	//Make all literals which are defined but do not occur in the theory false
	for(map<Atom, bool>::const_iterator i=defatoms.begin(); i!=defatoms.end(); i++){
		assert((*i).second);
		map<Atom, vector<BasicRule*> >::const_iterator it = headtorules.find((*i).first);
		if(it==headtorules.end() || (*it).second.size()==0){
			vector<Literal> lits;
			lits.push_back(Literal((*i).first, true));
			if(!getSolver()->addClause(lits)){
				return false;
			}
		}
	}
	return true;
}

bool Read::addOptimStatement(){
	if(optim){
		vector<Literal> optimheadclause;
		Literal optimhead = Literal(makeNewAtom());
		optimheadclause.push_back(optimhead);
		if(!getSolver()->addClause(optimheadclause)){
			return false;
		}
		if(!getSolver()->addSet(optimsetcount, optimbody, optimweights)){
			return false;
		}
		if(!getSolver()->addSumMinimize(optimhead.getAtom(), optimsetcount)){
			return false;
		}
	}
	return true;
}

bool Read::read(istream &f) {
	// Read rules.
	int type;
	bool stop = false, unsat = false;
	for (linenumber = 1; !stop && !unsat; linenumber++) {
		f >> type; // Rule Type
		switch (type) {
		case ENDRULE:
			stop = true;
			endedparsing = true;
			break;
		case BASICRULE:
			unsat = !parseBasicRule(f);
			break;
		case CONSTRAINTRULE:
			unsat = !parseConstraintRule(f);
			break;
		case CHOICERULE:
			unsat = !parseChoiceRule(f);
			break;
		case GENERATERULE:{
			char s[100];
			sprintf(s, "As, according to the lparse manual, \"generate rules cause semantical troubles\", we do not support them.\n");
			throw idpexception(s);
			break;
		}
		case WEIGHTRULE:
			unsat = !parseWeightRule(f);
			break;
		case OPTIMIZERULE:
			unsat = !parseOptimizeRule(f);
			break;
		default:{
			char s[100];
			sprintf(s, "Unsupported rule type: %d.\n", type);
			throw idpexception(s);
		}
		}
	}

	const int len = 1024;
	char s[len];
	long i;

	// Read atom names: lines ATOM NAME
	f.getline(s, len); // Get newline
	if (!f.good()) {
		char s[100];
		sprintf(s, "expected atom names to begin on new line %ld\n", linenumber);
		throw idpexception(s);
	}

	while(true){ //read until atom 0 read
		f >> i; //ATOM
		f.getline(s, len); //NAME
		linenumber++;
		if(i==0){
			break;
		}

		if (!f.good()) {
			char s[100];
			sprintf(s, "atom name too long or end of file, line %ld\n", linenumber);
			throw idpexception(s);
		}

		if(*s){
			translator->addTuple(Atom(i), s+1);
		}else{
			translator->addTuple(Atom(i), "");
		}
	}

	// Read compute-statement: B+ listposatoms 0 B- listnegatoms 0
	// listpostatoms are atoms that should all be true
	// listnegatoms are atoms that should all be false
	f.getline(s, len); //should be B+
	if (!f.good() || strcmp(s, "B+")!=0) {
		char s[100];
		sprintf(s, "B+ expected, line %ld\n", linenumber);
		throw idpexception(s);
	}
	linenumber++;
	while (true) {
		f >> i;
		linenumber++;
		if(i==0){
			break;
		}

		if (!f.good() || i < 1) {
			char s[100];
			sprintf(s, "B+ atom out of bounds, line %ld\n", linenumber);
			throw idpexception(s);
		}

		vector<Literal> lits;
		lits.push_back(Literal(makeParsedAtom(i)));
		if (!getSolver()->addClause(lits)) {
			return false;
		}
	}
	f.getline(s, len); // Read rest of last line (get newline);
	f.getline(s, len); //should be B-
	if (!f.good() || strcmp(s, "B-")!=0) {
		char s[100];
		sprintf(s, "B- expected, line %ld\n", linenumber);
		throw idpexception(s);
	}
	linenumber++;
	while (true) {
		f >> i;
		linenumber++;
		if(i==0){
			break;
		}
		if (!f.good() || i < 1) {
			char s[100];
			sprintf(s, "B- atom out of bounds, line %ld\n", linenumber);
			throw idpexception(s);
		}

		vector<Literal> lits;
		lits.push_back(Literal(makeParsedAtom(i), true));
		if (!getSolver()->addClause(lits)) {
			return false;
		}
	}

	f >> i; // nb of models, zero means all
	//FIXME is it safe to always ignore the number of models?

	if (f.fail()) {
		char s[100];
		sprintf(s, "number of models expected, line %ld\n", linenumber);
		throw idpexception(s);
	}

	unsat = !tseitinizeHeads();
	if(unsat) { return false; }
	unsat = !addBasicRules();
	if(unsat) { return false; }
	unsat = !addCardRules();
	if(unsat) { return false; }
	unsat = !addSumRules();
	if(unsat) { return false; }
	unsat = !addOptimStatement();
	if(unsat) { return false; }

	return true;
}