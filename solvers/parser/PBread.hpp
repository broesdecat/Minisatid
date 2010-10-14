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
#ifndef PBREAD_H
#define PBREAD_H

#include "solvers/external/ExternalInterface.hpp"

namespace MinisatID {
	struct Factor{
		std::vector<Literal> vars;
	};
}

#include <iostream>
#include <fstream>
#include <iomanip>
#include <stdexcept>
#include <vector>
#include <cassert>

#ifdef useGMP
#include <gmpxx.h>

namespace MinisatID {
	typedef	mpz_class IntegerType;
}
#else
#warning this IntegerType may not be suitable for some input file. Consider using GMP

namespace MinisatID {
	typedef long IntegerType;
}
#endif

namespace MinisatID {

class DefaultCallback {
private:
	PropositionalSolver* solver;
	PropositionalSolver* getSolver() { return solver; }

	IntegerType bound;
	bool equality;
	std::vector<LW> lw;
	int setid;
	int maxvar;

public:
	DefaultCallback(PropositionalSolver* solver):solver(solver), setid(0){

	}

	/**
	 * callback called when we get the number of variables and the
	 * expected number of constraints
	 * @param nbvar: the number of variables
	 * @param nbconstr: the number of contraints
	 */
	void metaData(int nbvar, int nbconstr);

	/**
	 * callback called before we read the objective function
	 */
	void beginObjective();

	/**
	 * callback called after we've read the objective function
	 */
	void endObjective();

	/**
	 * callback called when we read a term of the objective function
	 *
	 * @param coeff: the coefficient of the term
	 * @param idVar: the numerical identifier of the variable
	 */
	void objectiveTerm(IntegerType coeff, int idVar);

	/**
	 * callback called when we read a term of the objective function
	 * which is a product of literals
	 *
	 * @param coeff: the coefficient of the term
	 * @param list: list of literals which appear in the product
	 */
	void objectiveProduct(IntegerType coeff, std::vector<int> list);

	void beginConstraint();

	void endConstraint();

	/**
	 * callback called when we read a term of a constraint
	 *
	 * @param coeff: the coefficient of the term
	 * @param idVar: the numerical identifier of the variable
	 */
	void constraintTerm(IntegerType coeff, int idVar);

	/**
	 * callback called when we read a term of a constraint which is a
	 * product of literals
	 *
	 * @param coeff: the coefficient of the term
	 * @param list: list of literals which appear in the product
	 */
	void constraintProduct(IntegerType coeff, std::vector<int> list);

	/**
	 * callback called when we read the relational operator of a constraint
	 *
	 * @param relop: the relational oerator (>= or =)
	 */
	void constraintRelOp(std::string relop);

	/**
	 * callback called when we read the right term of a constraint (also
	 * known as the degree)
	 *
	 * @param val: the degree of the constraint
	 */
	void constraintRightTerm(IntegerType val);

	/**
	 * add the necessary constraints to define newSymbol as equivalent
	 * to the product (conjunction) of literals in product.
	 */
	void linearizeProduct(int newSymbol, std::vector<int> product);
};

/**
 * this class stores products of literals (as a tree) in order to
 * associate unique identifiers to these product (for linearization)
 */
class ProductStore {
private:
	// we represent each node of a n-ary tree by a std::vector<ProductNode>
	struct ProductNode {
		int lit; // ID of the literal
		int productId; // identifier associated to the product of the
		// literals found from the root up to this node
		std::vector<ProductNode> *next; // list of next literals in a product

		ProductNode(int l) {
			lit = l;
			productId = 0;
			next = NULL;
		}

		// if we define a destructor to free <next>, we'll have to define
		// a copy constructor and use reference counting. It's not worth it.
	};

	std::vector<ProductNode> root; // root of the n-ary tree
	int nextSymbol; // next available variable

	/**
	 * define an order on ProductNode based on the literal (used to
	 * speed up look up)
	 */
	class ProductNodeLessLit {
	public:
		bool operator ()(const ProductNode &a, const ProductNode &b) {
			return a.lit < b.lit;
		}
	};

public:
	/**
	 * give the first extra variable that can be used
	 */
	void setFirstExtraSymbol(int id) {
		nextSymbol = id;
	}

	/**
	 * get the identifier associated to a product term (update the list
	 * if necessary)
	 */
	int getProductVariable(std::vector<int> &list);

	void defineProductVariable(DefaultCallback &cb) {
		std::vector<int> list;
		defineProductVariableRec(cb, root, list);
	}
	void freeProductVariable() { freeProductVariableRec(root); }

private:
	void defineProductVariableRec(DefaultCallback &cb, std::vector<ProductNode> &nodes, std::vector<int> &list);
	void freeProductVariableRec(std::vector<ProductNode> &nodes);
};

class PBRead{
private:
	std::ifstream in; // the stream we're reading from
	int nbVars, nbConstr; // MetaData: #Variables and #Constraints in file.

	bool autoLinearize;
	int nbProduct, sizeProduct; // MetaData for non linear format
	ProductStore store;
	DefaultCallback cb;

public:
	PBRead(PropositionalSolver* solver, char *filename): cb(solver) {
		in.open(filename, std::ios_base::in);

		if (!in.good()){
			throw std::runtime_error("error opening input file");
		}

		autoLinearize = false;

		nbVars = 0;
		nbConstr = 0;
		nbProduct = 0;
		sizeProduct = 0;
	}

	~PBRead() {
		store.freeProductVariable();
	}

	void parse();
	void autoLin() { autoLinearize = true; }

private:
	char get	() 			{ return in.get(); }
	void putback(char c)	{ in.putback(c); }
	bool eof	()			{ return !in.good(); }

	void skipSpaces() {
		char c;
		while (isspace(c = get())) { ; }
		putback(c);
	}

	/**
	 * read an identifier from stream and append it to the list "list"
	 * @param list: the current list of identifiers that were read
	 * @return true iff an identifier was correctly read
	 */
	bool readIdentifier(std::vector<int> &list);

	/**
	 * read a relational operator from stream and store it in s
	 * @param s: the variable to hold the relational operator we read
	 * @return true iff a relational operator was correctly read
	 */
	bool readRelOp(std::string &s);

	/**
	 * read the first comment line to get the number of variables and
	 * the number of constraints in the file
	 *
	 * calls metaData with the data that was read
	 */
	void readMetaData();

	/**
	 * skip the comments at the beginning of the file
	 */
	void skipComments();

	/**
	 * read a term into coeff and list
	 * @param coeff: the coefficient of the variable
	 * @param list: the list of literals identifiers in the product
	 */
	void readTerm(IntegerType &coeff, std::vector<int> &list);

	/**
	 * read the objective line (if any)
	 *
	 * calls beginObjective, objectiveTerm and endObjective
	 */
	void readObjective();

	/**
	 * read a constraint
	 *
	 * calls beginConstraint, constraintTerm and endConstraint
	 */
	void readConstraint();

	/**
	 * passes a product term to the solver (first linearizes the product
	 * if this is wanted)
	 */
	void handleProduct(bool inObjective, IntegerType coeff, std::vector<int> &list);
};

}

#endif
