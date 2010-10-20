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

#include "solvers/parser/PBread.hpp"

#include <iostream>
#include <algorithm>
using namespace std;

using namespace MinisatID;

/*
 * callback called when we get the number of variables and the
 * expected number of constraints
 * @param nbvar: the number of variables
 * @param nbconstr: the number of contraints
 */
void DefaultCallback::metaData(int nbvar, int nbconstr) {
	maxvar = nbvar;
	cout << "[nbvar=" << nbvar << "]" << endl;
	cout << "[nbconstr=" << nbconstr << "]" << endl;
}

/**
 * callback called before we read the objective function
 */
void DefaultCallback::beginObjective() {
	report("Not yet supported");
	exit(1);
	cout << "objective:  ";
}

/**
 * callback called after we've read the objective function
 */
void DefaultCallback::endObjective() {
	//TODO
	cout << endl;
}

/**
 * callback called when we read a term of the objective function
 *
 * @param coeff: the coefficient of the term
 * @param idVar: the numerical identifier of the variable
 */
void DefaultCallback::objectiveTerm(IntegerType coeff, int idVar) {
	//TODO
	cout << "[" << showpos << coeff << noshowpos << " x" << idVar << "] ";
}

/**
 * callback called when we read a term of the objective function
 * which is a product of literals
 *
 * @param coeff: the coefficient of the term
 * @param list: list of literals which appear in the product
 */
void DefaultCallback::objectiveProduct(IntegerType coeff, vector<int> list) {
	//TODO
	cout << "[" << showpos << coeff << noshowpos << " ";
	for (int i = 0; i < list.size(); ++i) {
		if (list[i] < 0)
			cout << "~x" << -list[i] << ' ';
		else
			cout << "x" << list[i] << ' ';
	}
	cout << "] ";
}

void DefaultCallback::beginConstraint() {
	cout << "constraint: ";
}

void DefaultCallback::endConstraint() {
	setid++;
	getSolver()->addSet(setid, lw);
	lw.clear();
	int newvar = ++maxvar;
	vector<Literal> lits;
	if(equality){
		getSolver()->addAggrExpr(newvar, setid, bound, LB, SUM, COMP);
		lits.clear();
		lits.push_back(Literal(newvar));
		getSolver()->addClause(lits);
		newvar = ++maxvar;
		getSolver()->addAggrExpr(newvar, setid, bound, UB, SUM, COMP);
		lits.clear();
		lits.push_back(Literal(newvar));
		getSolver()->addClause(lits);
	}else{
		getSolver()->addAggrExpr(newvar, setid, bound, UB, SUM, COMP);
		lits.clear();
		lits.push_back(Literal(newvar));
		getSolver()->addClause(lits);
	}

	cout << endl;
}

/**
 * callback called when we read a term of a constraint
 *
 * @param coeff: the coefficient of the term
 * @param idVar: the numerical identifier of the variable
 */
void DefaultCallback::constraintTerm(IntegerType coeff, int idVar) {
	lw.push_back(WLtuple(Literal(abs(idVar), idVar<0), coeff));
	cout << "[" << showpos << coeff << noshowpos << " x" << idVar << "] ";
}

/**
 * callback called when we read a term of a constraint which is a
 * product of literals
 *
 * @param coeff: the coefficient of the term
 * @param list: list of literals which appear in the product
 */
void DefaultCallback::constraintProduct(IntegerType coeff, vector<int> list) {
	assert(false);
	cout << "[" << showpos << coeff << noshowpos << " ";
	for (int i = 0; i < list.size(); ++i) {
		if (list[i] < 0)
			cout << "~x" << -list[i] << ' ';
		else
			cout << "x" << list[i] << ' ';
	}
	cout << "] ";
}

/**
 * callback called when we read the relational operator of a constraint
 *
 * @param relop: the relational operator (>= or =)
 */
void DefaultCallback::constraintRelOp(string relop) {
	if(relop.compare("=")==0){
		equality = true;
	}else{
		equality = false;
	}
	cout << "[" << relop << "] ";
}

/**
 * callback called when we read the right term of a constraint (also
 * known as the degree)
 *
 * @param val: the degree of the constraint
 */
void DefaultCallback::constraintRightTerm(IntegerType val) {
	bound = val;
	cout << "[" << val << "]";
}

/**
 * add the necessary constraints to define newSymbol as equivalent
 * to the product (conjunction) of literals in product.
 */
void DefaultCallback::linearizeProduct(int newSymbol, vector<int> product) {
	IntegerType r;

	// product => newSymbol (this is a clause)
	// not x0 or not x1 or ... or not xn or newSymbol
	r = 1;
	beginConstraint();
	constraintTerm(1, newSymbol);
	for (int i = 0; i < product.size(); ++i)
		if (product[i] > 0) {
			constraintTerm(-1, product[i]);
			r -= 1;
		} else
			constraintTerm(1, -product[i]);
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
		endConstraint();
	}
#else
	// newSymbol => product translated as
	// x0+x1+x3...+xn-n*newSymbol>=0
	r = 0;
	beginConstraint();
	constraintTerm(-(int) product.size(), newSymbol);
	for (int i = 0; i < product.size(); ++i)
		if (product[i] > 0)
			constraintTerm(1, product[i]);
		else {
			constraintTerm(-1, -product[i]);
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
int ProductStore::getProductVariable(vector<int> &list) {
	vector<ProductNode> *p = &root;
	vector<ProductNode>::iterator pos;

	// list must be sorted
	sort(list.begin(), list.end());

	// is this a known product ?
	for (int i = 0; i < list.size(); ++i) {
		assert(p!=NULL);

		// look for list[i] in *p
		pos = lower_bound(p->begin(), p->end(), list[i], ProductNodeLessLit());
		if (pos == p->end() || (*pos).lit != list[i])
			pos = p->insert(pos, ProductNode(list[i])); // insert at the right place

		if (i != list.size() - 1 && (*pos).next == NULL)
			(*pos).next = new vector<ProductNode> ;

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
void ProductStore::defineProductVariableRec(DefaultCallback &cb, vector<ProductNode> &nodes, vector<int> &list) {
	for (int i = 0; i < nodes.size(); ++i) {
		list.push_back(nodes[i].lit);
		if (nodes[i].productId)
			cb.linearizeProduct(nodes[i].productId, list);

		if (nodes[i].next)
			defineProductVariableRec(cb, *nodes[i].next, list);

		list.pop_back();
	}
}

/**
 * free all allocated product data
 *
 */
void ProductStore::freeProductVariableRec(vector<ProductNode> &nodes) {
	for (int i = 0; i < nodes.size(); ++i) {
		if (nodes[i].next) {
			freeProductVariableRec(*nodes[i].next);
			delete nodes[i].next;
		}
	}

	nodes.clear();
}

/**
 * read an identifier from stream and append it to the list "list"
 * @param list: the current list of identifiers that were read
 * @return true iff an identifier was correctly read
 */
bool PBRead::readIdentifier(vector<int> &list) {
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
		throw runtime_error("variable identifier larger than "
			"#variables in metadata.");

	if (negated)
		varID = -varID;

	list.push_back(varID);

	return true;
}

/**
 * read a relational operator from stream and store it in s
 * @param s: the variable to hold the relational operator we read
 * @return true iff a relational operator was correctly read
 */
bool PBRead::readRelOp(string &s) {
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
void PBRead::readMetaData() {
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
	} else
		cb.metaData(nbVars, nbConstr);
}

/**
 * skip the comments at the beginning of the file
 */
void PBRead::skipComments() {
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
void PBRead::readTerm(IntegerType &coeff, vector<int> &list) {
	char c;
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
void PBRead::readObjective() {
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
			if (c == ';')
				break; // end of objective
			else if (c == '-' || c == '+' || isdigit(c))
				putback(c);
			else
				throw idpexception("unexpected character in objective function.\n");
		}

		cb.endObjective();
	} else
		throw idpexception("input format error: 'min:' expected.\n");
}

/**
 * read a constraint
 *
 * calls beginConstraint, constraintTerm and endConstraint
 */
void PBRead::readConstraint() {
	string s;
	char c;

	IntegerType coeff;
	vector<int> list;

	cb.beginConstraint();

	while (!eof()) {
		readTerm(coeff, list);
		if (list.size() == 1 && list[0] > 0)
			cb.constraintTerm(coeff, list[0]);
		else
			handleProduct(false, coeff, list);

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
void PBRead::handleProduct(bool inObjective, IntegerType coeff, vector<int> &list) {
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
void PBRead::parse() {
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
	if (nbConstraintsRead != nbConstr)
		throw idpexception("number of constraints read is different from metadata.\n");

	if (autoLinearize) {
		store.defineProductVariable(cb);
	}
}

