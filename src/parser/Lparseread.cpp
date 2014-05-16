/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */

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
#include <cstdio>

#include "parser/Lparseread.hpp"
#include "external/Translator.hpp"
#include "external/utils/ContainerUtils.hpp"
#include "external/Constraints.hpp"
#include "theorysolvers/PCSolver.hpp"

using namespace std;
using namespace MinisatID;

typedef enum {
	ENDRULE = 0,
	BASICRULE = 1,
	CONSTRAINTRULE = 2,
	CHOICERULE = 3,
	GENERATERULE = 4,
	WEIGHTRULE = 5,
	OPTIMIZERULE = 6
} RuleType;

template<class T>
Read<T>::~Read() {
	deleteList<BasicRule>(basicrules);
	deleteList<SumRule>(sumrules);
	deleteList<CardRule>(cardrules);
	deleteList<ChoiceRule>(choicerules);
}

template<class T>
Atom Read<T>::makeParsedAtom(int n) {
	Atom atom = makeAtom(n);
	pair<Atom, bool> p(atom, true);
	defatoms.insert(p);
	return atom;
}

template<class T>
Atom Read<T>::makeNewAtom() {
	MAssert(endedparsing);
	return makeAtom(++maxatomnumber);
}

template<class T>
Atom Read<T>::makeAtom(int n) {
	if (maxatomnumber < n) {
		maxatomnumber = n;
	}
	return Atom(n);
}

template<class T>
bool Read<T>::readBody(istream &f, long size, bool pos, vector<Lit>& body) {
	long n;
	for (long i = 0; i < size; ++i) {
		f >> n;
		if (!f.good() || n < 1) {
			char s[100];
			sprintf(s, "atom out of bounds, line %ld\n", linenumber);
			throw idpexception(s);
		}
		body.push_back(mkLit(makeParsedAtom(n), not pos));
	}
	return true;
}

template<class T>
bool Read<T>::readFullBody(istream &f, vector<Lit>& body) {
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

template<class T>
bool Read<T>::readWeights(std::istream &f, std::vector<Weight>& weights, int bodysize) {
	Weight sum = 0, w = 0;
	for (long i = 0; i < bodysize; ++i) {
		f >> w;
		if (!f.good()) {
			return false;
		}
		if ((w > 0 && posInfinity() - w < sum) || (w < 0 && negInfinity() - w > sum)) {
			char s[100];
			sprintf(s, "sum of weights in weight rule too large or too small, line %ld\n", linenumber);
			throw idpexception(s);
		}
		sum += w;
		weights.push_back(w);
	}
	return true;
}

template<class T>
bool Read<T>::parseBasicRule(istream &f) {
	long n;
	f >> n; // rule head
	if (!f.good() || n < 1) {
		char s[100];
		sprintf(s, "head atom out of bounds, line %ld\n", linenumber);
		throw idpexception(s);
	}
	Atom head = makeParsedAtom(n);

	vector<Lit> body;
	if (!readFullBody(f, body)) {
		return false;
	}

	basicrules.push_back(new BasicRule(head, body));
	return true;
}

template<class T>
bool Read<T>::parseConstraintRule(istream &f) {
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

	vector<Lit> body;
	if (!readBody(f, negbodysize, false, body)) { // Negative body: negated literals
		return false;
	}
	if (!readBody(f, bodysize - negbodysize, true, body)) { // Positive body
		return false;
	}

	cardrules.push_back(new CardRule(setcount++, head, body, Weight(atleast)));
	return true;
}

template<class T>
bool Read<T>::parseChoiceRule(istream &f) {
	long n;

	f >> n; // number of heads
	if (!f.good() || n < 1) {
		char s[100];
		sprintf(s, "head size less than one, line %ld\n", linenumber);
		throw idpexception(s);
	}
	long headssize = n;

	vector<Atom> heads;
	for (long i = 0; i < headssize; ++i) {
		f >> n;
		if (!f.good() || n < 1) {
			char s[100];
			sprintf(s, "atom out of bounds, line %ld\n", linenumber);
			throw idpexception(s);
		}
		heads.push_back(makeParsedAtom(n));
	}

	vector<Lit> body;
	if (!readFullBody(f, body)) {
		return false;
	}

	choicerules.push_back(new ChoiceRule(heads, body));
	return true;
}

template<class T>
bool Read<T>::parseWeightRule(istream &f) {
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

	vector<Lit> body;
	if (!readFullBody(f, body)) {
		return false;
	}

	vector<Weight> weights;
	if (!readWeights(f, weights, body.size())) {
		return false;
	}

	sumrules.push_back(new SumRule(setcount++, head, body, weights, lowerbound));
	return true;
}

template<class T>
bool Read<T>::parseOptimizeRule(istream &f) {
	long n;
	f >> n; // formerly choice between min or max, only 0 (minimize) still accepted
	if (!f.good())
		return false;
	if (n != 0) {
		char s[100];
		sprintf(s, "maximize statements are no longer accepted, line %ld\n", linenumber);
		throw idpexception(s);
	}

	vector<Lit> body;
	if (!readFullBody(f, body)) {
		return false;
	}

	//Weights
	vector<Weight> weights;
	if (!readWeights(f, weights, body.size())) {
		return false;
	}

	optim = true;
	optimbody = body;
	optimweights = weights;
	optimsetcount = setcount++;
	return true;
}

template<class T>
void Read<T>::addBasicRules() {
	for (auto i = basicrules.cbegin(); i < basicrules.cend(); ++i) {
		extAdd(getSolver(), Rule((*i)->head, (*i)->body, (*i)->conj, defaultdefinitionID, false));
	}
}

template<class T>
void Read<T>::addCardRules() {
	for (auto i = cardrules.cbegin(); i < cardrules.cend(); ++i) {
		extAdd(getSolver(), createSet((*i)->setcount, (*i)->body, 1));
		extAdd(getSolver(), Aggregate(mkPosLit((*i)->head), (*i)->setcount, (*i)->atleast, AggType::CARD, AggSign::LB, AggSem::DEF, defaultdefinitionID, false));
	}
}

template<class T>
void Read<T>::addSumRules() {
	for (auto i = sumrules.cbegin(); i < sumrules.cend(); ++i) {
		extAdd(getSolver(), createSet((*i)->setcount, (*i)->body, (*i)->weights));
		extAdd(getSolver(), Aggregate(mkPosLit((*i)->head), (*i)->setcount, (*i)->atleast, AggType::SUM, AggSign::LB, AggSem::DEF, defaultdefinitionID, false));
	}
}

template<class T>
void Read<T>::addRuleToHead(std::map<Atom, std::vector<BasicRule*> >& headtorules, BasicRule* rule, Atom head) {
	if (headtorules.find(head) == headtorules.cend()) {
		headtorules.insert(pair<Atom, vector<BasicRule*> >(head, std::vector<BasicRule*>()));
	}
	(*headtorules.find(head)).second.push_back(rule);
}

template<class T>
void Read<T>::tseitinizeHeads() {
	// Transform away all choicerules
	for (auto i = choicerules.cbegin(); i < choicerules.cend(); ++i) {
		vector<Lit> tempbody;
		tempbody.push_back(mkPosLit(1)); //reserve space for the extra choice literal
		tempbody.insert(tempbody.end(), (*i)->body.cbegin(), (*i)->body.cend());
		for (auto j = (*i)->heads.cbegin(); j < (*i)->heads.cend(); ++j) {
			auto head = *j;
			tempbody[0] = mkPosLit(makeNewAtom());
			basicrules.push_back(new BasicRule(head, tempbody));

			//To guarantee #model equivalence:
			Implication eq(tempbody[0], ImplicationType::EQUIVALENT, { mkPosLit(head) }, true);
			extAdd(getSolver(), eq);
		}
	}

	//Check whether there are multiple occurrences and rewrite them using tseitin!
	std::map<Atom, std::vector<BasicRule*> > headtorules;
	for (auto i = basicrules.cbegin(); i < basicrules.cend(); ++i) {
		addRuleToHead(headtorules, *i, (*i)->head);
	}
	for (auto i = cardrules.cbegin(); i < cardrules.cend(); ++i) {
		addRuleToHead(headtorules, *i, (*i)->head);
	}
	for (auto i = sumrules.cbegin(); i < sumrules.cend(); ++i) {
		addRuleToHead(headtorules, *i, (*i)->head);
	}

	//Make all literals which are defined but do not occur in the theory false
	for (auto i = defatoms.cbegin(); i != defatoms.cend(); ++i) {
		MAssert((*i).second);
		auto it = headtorules.find((*i).first);
		if (it == headtorules.cend() || (*it).second.size() == 0) {
			Disjunction clause( { mkNegLit((*i).first) });
			extAdd(getSolver(), clause);
		}
	}
}

template<class T>
void Read<T>::addOptimStatement() {
	if (optim) {
		vector<Lit> optimheadclause;
		extAdd(getSolver(), createSet(optimsetcount, optimbody, optimweights));
		extAdd(getSolver(), MinimizeAgg(1, optimsetcount, AggType::SUM));
	}
}

template<class T>
bool Read<T>::read(istream &f) {
	// Read rules.
	int type;
	bool stop = false, unsat = false;
	for (linenumber = 1; !stop && !unsat; ++linenumber) {
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
		case GENERATERULE: {
			char s[200];
			sprintf(s, "As, according to the lparse manual, \"generate rules cause semantical troubles\", they are not supported.\n");
			throw idpexception(s);
			break;
		}
		case WEIGHTRULE:
			unsat = !parseWeightRule(f);
			break;
		case OPTIMIZERULE:
			unsat = !parseOptimizeRule(f);
			break;
		default: {
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

	while (true) { //read until atom 0 read
		f >> i; //ATOM
		f.getline(s, len); //NAME
		linenumber++;
		if (i == 0) {
			break;
		}

		if (!f.good()) {
			char s[100];
			sprintf(s, "atom name too long or end of file, line %ld\n", linenumber);
			throw idpexception(s);
		}

		if (*s) {
			translator->setString(Atom(i), s + 1);
		} else {
			translator->setString(Atom(i), "");
		}
	}

	// Read compute-statement: B+ listposatoms 0 B- listnegatoms 0
	// listpostatoms are atoms that should all be true
	// listnegatoms are atoms that should all be false
	f.getline(s, len); //should be B+
	if (!f.good() || strcmp(s, "B+") != 0) {
		char s[100];
		sprintf(s, "B+ expected, line %ld\n", linenumber);
		throw idpexception(s);
	}
	linenumber++;
	while (true) {
		f >> i;
		linenumber++;
		if (i == 0) {
			break;
		}

		if (!f.good() || i < 1) {
			char s[100];
			sprintf(s, "B+ atom out of bounds, line %ld\n", linenumber);
			throw idpexception(s);
		}

		Disjunction clause( { mkPosLit(makeParsedAtom(i)) });
		extAdd(getSolver(), clause);
	}
	f.getline(s, len); // Read rest of last line (get newline);
	f.getline(s, len); //should be B-
	if (!f.good() || strcmp(s, "B-") != 0) {
		char s[100];
		sprintf(s, "B- expected, line %ld\n", linenumber);
		throw idpexception(s);
	}
	linenumber++;
	while (true) {
		f >> i;
		linenumber++;
		if (i == 0) {
			break;
		}
		if (!f.good() || i < 1) {
			char s[100];
			sprintf(s, "B- atom out of bounds, line %ld\n", linenumber);
			throw idpexception(s);
		}

		Disjunction clause( { mkNegLit(makeParsedAtom(i)) });
		extAdd(getSolver(), clause);
	}

	f >> i; // nb of models, zero means all
	clog << ">> Number of models in the lparse input is always ignored.\n";

	if (f.fail()) {
		char s[100];
		sprintf(s, "number of models expected, line %ld\n", linenumber);
		throw idpexception(s);
	}

	tseitinizeHeads();
	addBasicRules();
	addCardRules();
	addSumRules();
	addOptimStatement();

	return true;
}
