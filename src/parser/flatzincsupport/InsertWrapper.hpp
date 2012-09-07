/*
 * Copyright 2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef INSERTWRAPPER_HPP_
#define INSERTWRAPPER_HPP_

#include <vector>
#include <string>
#include <sstream>
#include <map>
#include "FZDatastructs.hpp"

namespace MinisatID{
	class ExternalConstraintVisitor;
}

namespace FZ {

enum CONSTRAINT_TYPE {
	bool2int,

	booland,
	boolclause,
	booleq,
	booleqr,
	boolle,
	booller,
	boollt,
	boolltr,
	boolnot,
	boolor,
	boolxor,

	intabs,
	intdiv,
	inteq,
	inteqr,
	intle,
	intler,
	intlt,
	intltr,
	intmax,
	intmin,
	intmod,
	intne,
	intner,
	intplus,
	inttimes,
	intlineq,
	intlineqr,
	intlinle,
	intlinler,
	intlinne,
	intlinner,

	arraybooland,
	arrayboolor,
	arrayboolxor,
	arrayboolelem,
	arrayintelem,
	arrayvarboolelem,
	arrayvarintelem,

	setin,
	setinr
};

enum ARG_TYPE {
	ARG_BOOL, ARG_INT, ARG_SET, ARG_ARRAY_OF_SET, ARG_ARRAY_OF_INT, ARG_ARRAY_OF_BOOL
};

class InsertWrapper {
private:
	Storage* storage;
	std::map<std::string, CONSTRAINT_TYPE> name2type;
	void addFunc(const std::string& func, const std::vector<Expression*>& origargs);
	void parseArgs(const std::vector<Expression*>& origargs, std::vector<int>& args, const std::vector<ARG_TYPE>& expectedtypes);

	MIntVar* createNegation(const MIntVar& var);
	void addOptim(Expression& expr, bool maxim);

public:
	InsertWrapper(MinisatID::ExternalConstraintVisitor* storage);
	virtual ~InsertWrapper();

	bool isCertainlyUnsat() const;

	void add(Var* var);
	void add(Constraint* var);
	void add(Search* var);
};
}

#endif /* INSERTWRAPPER_HPP_ */
