/*
 * Copyright 2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef FZDATASTRUCTS_HPP_
#define FZDATASTRUCTS_HPP_

#include <string>
#include <vector>
#include <sstream>
#include <map>

namespace FZ {

typedef unsigned int uint;

class Storage;

template<typename T>
std::string term(const std::string& name, const T& arg1) {
	std::stringstream ss;
	ss << name << "(" << arg1 << ")";
	return ss.str();
}

template<typename T, typename T2>
std::string term(const std::string& name, const T& arg1, const T2& arg2) {
	std::stringstream ss;
	ss << name << "(" << arg1 << ", " << arg2 << ")";
	return ss.str();
}

template<typename T>
void deleteList(std::vector<T*>* list) {
	if (list == NULL) {
		return;
	}
	for (auto i = list->begin(); i < list->end(); ++i) {
		if ((*i) != NULL) {
			delete *i;
		}
	}
	delete (list);
}

struct Expression;

struct Identifier {
	std::string* name;
	std::vector<Expression*>* arguments;

	Identifier(std::string* name, std::vector<Expression*>* arguments)
			: name(name), arguments(arguments) {
	}
	~Identifier() {
		if (name != NULL) {
			delete (name);
		}
		if (arguments != NULL) {
			deleteList(arguments);
		}
	}
};

struct ArrayAccess {
	std::string* id;
	int index;

	ArrayAccess(std::string* id, int index)
			: id(id), index(index) {
	}
	~ArrayAccess() {
		if (id != NULL) {
			delete (id);
		}
	}
};

struct ArrayLiteral {
	std::vector<Expression*>* exprs;

	ArrayLiteral()
			: exprs(new std::vector<Expression*>()) {
	}
	~ArrayLiteral() {
		if (exprs != NULL) {
			deleteList(exprs);
		}
	}
};

struct SetLiteral {
	bool range;
	std::vector<Expression*>* values;
	int begin, end;

	SetLiteral(std::vector<Expression*>* values)
			: range(false), values(values), begin(0), end(0) {
	}
	SetLiteral(int begin, int end)
			: range(true), values(NULL), begin(begin), end(end) {
	}
	~SetLiteral() {
		if (values != NULL) {
			delete (values);
		}
	}
};

enum EXPR_TYPE {
	EXPR_BOOL, EXPR_INT, EXPR_SET, EXPR_ARRAY, EXPR_FLOAT, EXPR_STRING, EXPR_ARRAYACCESS, EXPR_IDENT
};

std::ostream& operator<<(std::ostream&, EXPR_TYPE type);

struct Expression {
	EXPR_TYPE type;
	bool boollit;
	int intlit;
	float floatlit;
	Identifier* ident;
	ArrayAccess* arrayaccesslit;
	ArrayLiteral* arraylit;
	SetLiteral* setlit;
	std::string* stringlit; // only for annotations

	Expression()
			: type(EXPR_BOOL), boollit(false), intlit(0), floatlit(0), ident(NULL), arrayaccesslit(NULL), arraylit(NULL), setlit(NULL), stringlit(NULL) {
	}
	~Expression() {
		if (ident != NULL) {
			delete (ident);
		}
		if (arrayaccesslit != NULL) {
			delete (arrayaccesslit);
		}
		if (arraylit != NULL) {
			delete (arraylit);
		}
		if (setlit != NULL) {
			delete (setlit);
		}
		if (stringlit != NULL) {
			delete (stringlit);
		}
	}

	std::string toString() const {
		switch (type) {
		case EXPR_TYPE::EXPR_ARRAY:
			return "expr_array";
		case EXPR_TYPE::EXPR_ARRAYACCESS:
			return "expr_arrayaccess";
		case EXPR_TYPE::EXPR_BOOL:
			return "expr_bool";
		case EXPR_TYPE::EXPR_FLOAT:
			return "expr_float";
		case EXPR_TYPE::EXPR_IDENT:
			return "expr_ident";
		case EXPR_TYPE::EXPR_INT:
			return "expr_int";
		case EXPR_TYPE::EXPR_SET:
			return "expr_set";
		case EXPR_TYPE::EXPR_STRING:
			return "expr_string";
		}
	}
};

struct MBoolVar {
	int var;

	bool hasvalue, value;
	bool hasmap;
	MBoolVar* mappedvar;

	bool hasValue() const {
		return hasvalue || (hasmap && mappedvar->hasValue());
	}
	bool getValue() const;
};

struct MIntVar {
	uint var;

	bool hasmap, hasvalue; //Not both of them true
	int value;
	MIntVar* mappedvar;

	bool range; //Not range implies enumerated values
	int begin, end;
	std::vector<int> values;

	void set(bool r, int b, int e) {
		range = r;
		begin = b;
		end = e;
	}

	bool hasValue() const {
		return hasvalue || (hasmap && mappedvar->hasValue());
	}
	int getValue() const;
};

struct MSetVar{
	bool isrange;
	int start, end;
	std::vector<int> values;
};

template<class Var>
struct MArrayVar {
	std::vector<Var*> vars;
};

enum VAR_TYPE {
	VAR_BOOL, VAR_INT, VAR_SET, VAR_FLOAT, VAR_ARRAY
};

class Var {
public:
	bool output;
	std::string outputname;
	bool var;
	VAR_TYPE type;
	Identifier* id;
	Expression* expr;
	Var(VAR_TYPE type)
			: output(false), var(true), type(type), id(NULL), expr(NULL) {
	}
	virtual ~Var() {
		if (id != NULL) {
			delete (id);
		}
		if (expr != NULL) {
			delete (expr);
		}
	}

	bool isOutput() const {
		return output;
	}
	void setOutput() {
		output = true;
	}
	const std::string& getOutputName() const {
		return isOutput() ? outputname : getName();
	}
	void setOutputName(const std::string& name) {
		outputname = name;
	}

	const std::string& getName() const {
		return *id->name;
	}

	virtual void add(Storage& storage);
};

class IntVar: public Var {
public:
	bool range;
	bool enumvalues;
	int begin, end;
	std::vector<int>* values;

	IntVar()
			: Var(VAR_INT), range(false), enumvalues(false), begin(0), end(0), values(NULL) {
	}
	IntVar(int begin, int end)
			: Var(VAR_INT), range(true), enumvalues(false), begin(begin), end(end), values(NULL) {
	}
	IntVar(std::vector<int>* values)
			: Var(VAR_INT), range(false), enumvalues(true), begin(0), end(0), values(values) {
	}
	virtual ~IntVar() {
		if (values != NULL) {
			delete (values);
		}
	}

	void add(Storage& storage);
};

class SetVar: public Var {
private:
	std::vector<int> values;
public:
	IntVar* var;
	bool isrange;
	int start, end;

	SetVar(IntVar* var)
			: Var(VAR_SET), var(var) {
	}
	virtual ~SetVar() {
		delete (var);
	}

	void add(Storage& storage);

	const std::vector<int> getValues() const { return values; }
	void setValues(const std::vector<int>& v) { values = v;}
};

class ArrayVar: public Var {
public:
	int begin, end; // NOTE are set LATER than constructor

	// Important: if rangevar is NULL, the type indicates the basetype of the array and it HAS to have an arraylist instantiating it
	Var* rangevar; //the type the array maps to
	VAR_TYPE rangetype; //

	ArrayLiteral* arraylit; //What the array is assigned to
	//IMPORTANT: expr field has no value here!

	ArrayVar(Var* rangevar)
			: Var(VAR_ARRAY), begin(-1), end(-1), rangevar(rangevar), rangetype(rangevar->type), arraylit(NULL) {
	}
	ArrayVar(Var* rangevar, ArrayLiteral* arraylit)
			: Var(VAR_ARRAY), begin(-1), end(-1), rangevar(rangevar), rangetype(rangevar->type), arraylit(arraylit) {
	}
	ArrayVar(VAR_TYPE rangetype, ArrayLiteral* arraylit)
			: Var(VAR_ARRAY), begin(-1), end(-1), rangevar(NULL), rangetype(rangetype), arraylit(arraylit) {
	}

	virtual ~ArrayVar() {
		if (rangevar != NULL) {
			delete (rangevar);
		}
		if (arraylit != NULL) {
			delete (arraylit);
		}
	}

	void add(Storage& storage);
};

enum SOLVE_TYPE {
	SOLVE_SATISFY, SOLVE_MINIMIZE, SOLVE_MAXIMIZE
};
struct Search {
	SOLVE_TYPE type;
	Expression* expr;
	std::vector<Expression*>* annotations;

	Search(SOLVE_TYPE type, Expression* expr)
			: type(type), expr(expr), annotations(NULL) {
	}
	~Search() {
		if (expr != NULL) {
			delete (expr);
		}
		if (annotations != NULL) {
			deleteList(annotations);
		}
	}
};

struct Constraint {
	Identifier* id;
	std::vector<Expression*>* annotations;

	Constraint(Identifier* id)
			: id(id), annotations(NULL) {
	}
	~Constraint() {
		if (id != NULL) {
			delete (id);
		}
		if (annotations != NULL) {
			deleteList(annotations);
		}
	}
};

int parseBool(Storage& storage, const Expression& expr);
int parseInt(Storage& storage, const Expression& expr);
MSetVar* parseSet(Storage& storage, const Identifier& ident);
int parseParInt(Storage& storage, const Expression& expr);
bool parseParBool(Storage& storage, const Expression& expr);
std::vector<int> parseParIntArray(Storage& storage, Expression& expr);
std::vector<bool> parseParBoolArray(Storage& storage, Expression& expr);

bool isRangeSet(const Expression& expr);
std::pair<int, int> parseParRangeSet(const Expression& expr);
std::vector<int> parseParValueSet(Storage& storage, const Expression& expr);

std::vector<int> parseBoolArray(Storage& storage, Expression& expr);
std::vector<uint> parseIntArray(Storage& storage, Expression& expr);

}

#endif /* FZDATASTRUCTS_HPP_ */
