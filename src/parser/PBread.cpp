/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
/*=============================================================================
 * parser for pseudo-Boolean instances
 *
 * Copyright (c) 2005-2007 Olivier ROUSSEL and Vasco MANQUINHO
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 *=============================================================================
 */

// version 2.9.4

#include "parser/PBread.hpp"
#include "external/Constraints.hpp"
#include "theorysolvers/PCSolver.hpp"

#include <sstream>
#include <iostream>
#include <stdlib.h>
#include <algorithm>

using namespace std;

using namespace MinisatID;

/*
 * callback called when we get the number of variables and the
 * expected number of constraints
 * @param nbvar: the number of variables
 * @param nbconstr: the number of contraints
 */
template<class T> void DefaultCallback<T>::metaData(int nbvar, int) {
	maxvar = nbvar;
	dummyhead = Atom(++maxvar);
	Disjunction clause({mkPosLit(dummyhead)});
	extAdd(getSolver(), clause);
}

/**
 * callback called before we read the objective function
 */
template<class T> void DefaultCallback<T>::beginObjective() {

}

/**
 * callback called after we've read the objective function
 */
template<class T> void DefaultCallback<T>::endObjective() {
	extAdd(getSolver(), wset);
	extAdd(getSolver(), MinimizeAgg(1, wset.setID, AggType::SUM));
	wset = WLSet(++setid);
}

/**
 * callback called when we read a term of the objective function
 *
 * @param coeff: the coefficient of the term
 * @param idVar: the numerical identifier of the variable
 */
template<class T> void DefaultCallback<T>::objectiveTerm(IntegerType coeff, int idVar) {
	wset.wl.push_back({createLiteralFromOPBVar(idVar), Weight(coeff)});
}

/**
 * callback called when we read a term of the objective function
 * which is a product of literals
 *
 * @param coeff: the coefficient of the term
 * @param list: list of literals which appear in the product
 */
template<class T> void DefaultCallback<T>::objectiveProduct(IntegerType, vector<int>) {
	throw idpexception("Linearization of opb constraints is mandatory\n!");
}

template<class T> void DefaultCallback<T>::beginConstraint() {
	//cout << "constraint: ";
	MAssert(wset.wl.size()==0);
}

template<class T> void DefaultCallback<T>::endConstraint() {
	extAdd(getSolver(), wset);
	Aggregate agg(mkPosLit(dummyhead), wset.setID, bound, AggType::SUM, AggSign::LB, AggSem::COMP, -1, false);
	if(equality){
		agg.sign = AggSign::LB;
		extAdd(getSolver(), agg);
		agg.sign = AggSign::UB;
		extAdd(getSolver(), agg);
	}else{
		agg.sign = AggSign::LB;
		extAdd(getSolver(), agg);
	}
	wset = WLSet(++setid);
}

template<class T> Lit DefaultCallback<T>::createLiteralFromOPBVar(int var){
	return mkLit(::abs(var), var<0);
}

/**
 * callback called when we read a term of a constraint
 *
 * @param coeff: the coefficient of the term
 * @param idVar: the numerical identifier of the variable
 */
template<class T> void DefaultCallback<T>::constraintTerm(IntegerType coeff, int idVar) {
	wset.wl.push_back({createLiteralFromOPBVar(idVar), Weight(coeff)});
}

/**
 * callback called when we read a term of a constraint which is a
 * product of literals
 *
 * @param coeff: the coefficient of the term
 * @param list: list of literals which appear in the product
 */
template<class T> void DefaultCallback<T>::constraintProduct(IntegerType, vector<int>) {
	throw idpexception("Linearization of opb constraints is mandatory!\n");
}

/**
 * callback called when we read the relational operator of a constraint
 *
 * @param relop: the relational operator (>= or =)
 */
template<class T> void DefaultCallback<T>::constraintRelOp(string relop) {
	if(relop.compare("=")==0){
		equality = true;
	}else{
		equality = false;
	}
}

/**
 * callback called when we read the right term of a constraint (also
 * known as the degree)
 *
 * @param val: the degree of the constraint
 */
template<class T> void DefaultCallback<T>::constraintRightTerm(IntegerType val) {
	bound = val;
}

/**
 * add the necessary constraints to define newSymbol as equivalent
 * to the product (conjunction) of literals in product.
 */
template<class T> void DefaultCallback<T>::linearizeProduct(int newSymbol, vector<int> product) {
	IntegerType r;

	// product => newSymbol (this is a clause)
	// not x0 or not x1 or ... or not xn or newSymbol
	r = 1;
	beginConstraint();
	constraintTerm(1, newSymbol);
	for (auto i =product.cbegin(); i < product.cend(); ++i)
		if (*i > 0) {
			constraintTerm(-1, *i);
			r -= 1;
		} else
			constraintTerm(1, -(*i));
	constraintRelOp(">=");
	constraintRightTerm(r);
	endConstraint();

#ifdef ONLYCLAUSES
	// newSymbol => product translated as
	// not newSymbol of xi (for all i)
	for(int i=0;i<product.size();++i)
	{
		r=0;
		beginConstraint();
		constraintTerm(-1,newSymbol);
		if (product[i]>0)
		constraintTerm(1,product[i]);
		else
		{
			constraintTerm(-1,-product[i]);
			r-=1;
		}
		constraintRelOp(">=");
		constraintRightTerm(r);
		possat &= endConstraint();
	}
#else
	// newSymbol => product translated as
	// x0+x1+x3...+xn-n*newSymbol>=0
	r = 0;
	beginConstraint();
	constraintTerm(-(int) product.size(), newSymbol);
	for (auto i =product.cbegin(); i < product.cend(); ++i)
		if (*i > 0)
			constraintTerm(1, *i);
		else {
			constraintTerm(-1, -(*i));
			r -= 1;
		}
	constraintRelOp(">=");
	constraintRightTerm(r);
	endConstraint();
#endif
}

/**
 * get the identifier associated to a product term (update the list
 * if necessary)
 */
template<class T> int ProductStore<T>::getProductVariable(vector<int> &list) {
	vector<ProductNode> *p = &root;
	typename vector<ProductNode>::iterator pos;

	// list must be sorted
	sort(list.begin(), list.end());

	// is this a known product ?
	for (auto i =list.cbegin(); i < list.cend(); ++i){
		MAssert(p!=NULL);

		// look for list[i] in *p
		pos = lower_bound(p->begin(), p->end(), *i, ProductNodeLessLit());
		if (pos == p->end() || (*pos).lit != *i)
			pos = p->insert(pos, ProductNode(*i)); // insert at the right place

		if(i+1 != list.cend() && (*pos).next == NULL){
			(*pos).next = new vector<ProductNode> ;
		}

		p = (*pos).next;
	}

	if ((*pos).productId == 0)
		(*pos).productId = nextSymbol++;

	return (*pos).productId;
}

/**
 * add the constraints which define all product terms
 *
 */
template<class T> void ProductStore<T>::defineProductVariableRec(DefaultCallback<T> &cb, vector<ProductNode> &nodes, vector<int> &list) {
	for (typename vector<ProductNode>::const_iterator i = nodes.cbegin(); i < nodes.cend(); ++i) {
		list.push_back((*i).lit);
		if ((*i).productId){
			cb.linearizeProduct((*i).productId, list);
		}

		if ((*i).next){
			defineProductVariableRec(cb, *(*i).next, list);
		}

		list.pop_back();
	}
}

/**
 * free all allocated product data
 *
 */
template<class T> void ProductStore<T>::freeProductVariableRec(vector<ProductNode> &nodes) {
	for (typename vector<ProductNode>::const_iterator i = nodes.cbegin(); i < nodes.cend(); ++i) {
		if ((*i).next) {
			freeProductVariableRec(*(*i).next);
			delete (*i).next;
		}
	}

	nodes.clear();
}

/**
 * read an identifier from stream and append it to the list "list"
 * @param list: the current list of identifiers that were read
 * @return true iff an identifier was correctly read
 */
template<class T> bool PBRead<T>::readIdentifier(vector<int> &list) {
	char c;
	bool negated = false;

	skipSpaces();

	// first char (must be 'x')
	c = get();
	if (eof())
		return false;

	if (c == '~') {
		negated = true;
		c = get();
	}

	if (c != 'x') {
		putback(c);
		return false;
	}

	int varID = 0;

	// next chars (must be digits)
	while (true) {
		c = get();
		if (eof())
			break;

		if (isdigit(c))
			varID = varID * 10 + c - '0';
		else {
			putback(c);
			break;
		}
	}

	//Small check on the coefficient ID to make sure everything is ok
	if (varID > nbVars)
		throw runtime_error("variable identifier larger than #variables in metadata.");

	if (negated)
		varID = -varID;

	list.push_back(varID);

	stringstream ss;
	ss <<"x" <<::abs(varID);
	getTranslator().setString(Atom(::abs(varID)), ss.str());

	return true;
}

/**
 * read a relational operator from stream and store it in s
 * @param s: the variable to hold the relational operator we read
 * @return true iff a relational operator was correctly read
 */
template<class T> bool PBRead<T>::readRelOp(string &s) {
	char c;

	skipSpaces();

	c = get();
	if (eof())
		return false;

	if (c == '=') {
		s = "=";
		return true;
	}

	if (c == '>' && get() == '=') {
		s = ">=";
		return true;
	}

	return false;
}

/**
 * read the first comment line to get the number of variables and
 * the number of constraints in the file
 *
 * calls metaData with the data that was read
 */
template<class T> void PBRead<T>::readMetaData() {
	char c;
	string s;

	// get the number of variables and constraints
	c = get();
	if (c != '*')
		throw idpexception("First line of input file should be a comment.\n");

	in >> s;
	if (eof() || s != "#variable=")
		throw idpexception("First line should contain #variable= as first keyword.\n");

	in >> nbVars;
	store.setFirstExtraSymbol(nbVars + 1);

	in >> s;
	if (eof() || s != "#constraint=")
		throw idpexception("First line should contain #constraint= as second keyword.\n");

	in >> nbConstr;

	skipSpaces();

	c = get();
	putback(c);

	if (c == '#') {
		// assume non linear format
		in >> s;
		if (eof() || s != "#product=")
			throw idpexception("First line should contain #product= as third keyword.\n");

		in >> nbProduct;

		in >> s;
		if (eof() || s != "sizeproduct=")
			throw idpexception("First line should contain sizeproduct= as fourth keyword.\n");

		in >> sizeProduct;
	}

	// skip the rest of the line
	getline(in, s);

	// callback to transmit the data
	if (nbProduct && autoLinearize) {
#ifdef ONLYCLAUSES
		cb.metaData(nbVars+nbProduct,nbConstr+nbProduct+sizeProduct);
#else
		cb.metaData(nbVars + nbProduct, nbConstr + 2 * nbProduct);
#endif
	} else{
		cb.metaData(nbVars, nbConstr);
	}
}

/**
 * skip the comments at the beginning of the file
 */
template<class T> void PBRead<T>::skipComments() {
	string s;
	char c;

	// skip further comments

	while (!eof() && (c = get()) == '*') {
		getline(in, s);
	}

	putback(c);
}

/**
 * read a term into coeff and list
 * @param coeff: the coefficient of the variable
 * @param list: the list of literals identifiers in the product
 */
template<class T> void PBRead<T>::readTerm(IntegerType &coeff, vector<int> &list) {
	list.clear();
	in >> coeff;
	skipSpaces();

	while (readIdentifier(list))
		;

	if (list.size() == 0)
		throw idpexception("identifier expected.\n");
}

/**
 * read the objective line (if any)
 *
 * calls beginObjective, objectiveTerm and endObjective
 */
template<class T> void PBRead<T>::readObjective() {
	char c;
	string s;

	IntegerType coeff;
	vector<int> list;

	// read objective line (if any)

	skipSpaces();
	c = get();
	if (c != 'm') {
		// no objective line
		putback(c);
		return;
	}

	if (get() == 'i' && get() == 'n' && get() == ':') {
		cb.beginObjective(); // callback

		while (!eof()) {
			readTerm(coeff, list);
			if (list.size() == 1 && list[0] > 0)
				cb.objectiveTerm(coeff, list[0]);
			else
				handleProduct(true, coeff, list);

			skipSpaces();
			c = get();
			if (c == ';'){
				break; // end of objective
			}
			else if (c == '-' || c == '+' || isdigit(c)){
				putback(c);
			} else{
				throw idpexception("unexpected character in objective function.\n");
			}
		}

		cb.endObjective();
	} else{
		throw idpexception("input format error: 'min:' expected.\n");
	}
}

/**
 * read a constraint
 *
 * calls beginConstraint, constraintTerm and endConstraint
 */
template<class T> void PBRead<T>::readConstraint() {
	string s;
	char c;

	IntegerType coeff;
	vector<int> list;

	cb.beginConstraint();

	while (!eof()) {
		readTerm(coeff, list);
		if (list.size() == 1 && list[0] > 0){ // NOTE: only vars x1 or larger are allowed!
			cb.constraintTerm(coeff, list[0]);
		}else{
			handleProduct(false, coeff, list);
		}

		skipSpaces();
		c = get();
		if (c == '>' || c == '=') {
			// relational operator found
			putback(c);
			break;
		} else if (c == '-' || c == '+' || isdigit(c))
			putback(c);
		else
			throw idpexception("unexpected character in constraint.\n");
	}

	if (eof())
		throw idpexception("unexpected EOF before end of constraint.\n");

	if (readRelOp(s))
		cb.constraintRelOp(s);
	else
		throw idpexception("unexpected relational operator in constraint.\n");

	in >> coeff;
	cb.constraintRightTerm(coeff);

	skipSpaces();
	c = get();
	if (eof() || c != ';')
		throw idpexception("semicolon expected at end of constraint.\n");

	cb.endConstraint();
}

/**
 * passes a product term to the solver (first linearizes the product
 * if this is wanted)
 */
template<class T> void PBRead<T>::handleProduct(bool inObjective, IntegerType coeff, vector<int> &list) {
	if (autoLinearize) {
		// get symbol corresponding to this product
		int var = store.getProductVariable(list);

		if (inObjective)
			cb.objectiveTerm(coeff, var);
		else
			cb.constraintTerm(coeff, var);
	} else {
		if (inObjective)
			cb.objectiveProduct(coeff, list);
		else
			cb.constraintProduct(coeff, list);
	}
}

/**
 * parses the file and uses the callbacks to send the data
 * back to the program
 */
template<class T> void PBRead<T>::parse() {
	char c;

	readMetaData();
	skipComments();
	readObjective();

	// read constraints
	int nbConstraintsRead = 0;
	while (!eof()) {
		skipSpaces();
		if (eof())
			break;

		putback(c = get());
		if (c == '*')
			skipComments();

		if (eof())
			break;

		readConstraint();
		nbConstraintsRead++;
	}

	//Small check on the number of constraints
	if (nbConstraintsRead != nbConstr){
		char s[100]; sprintf(s, "number of constraints read is different from metadata: %d aot %d.\n", nbConstraintsRead, nbConstr);
		throw idpexception(s);
	}

	if (autoLinearize) {
		store.defineProductVariable(cb);
	}
}

