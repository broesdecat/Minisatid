/*
 * Copyright 2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#include "FZDatastructs.hpp"

#include <cassert>

#include "Storage.hpp"
#include "fzexception.hpp"

using namespace std;
using namespace FZ;

int nextint = 1;
std::map<std::string, MBoolVar*> name2bool;
std::map<std::string, MIntVar*> name2int;
std::map<std::string, MBoolArrayVar*> name2boolarray;
std::map<std::string, MIntArrayVar*> name2intarray;

MBoolVar* createBoolVar(const string& name) {
	auto var = new MBoolVar();
	var->var = nextint++;
	var->hasmap = false;
	var->hasvalue = false;
	name2bool.insert({name, var});
	return var;
}

int FZ::createOneShotVar() {
	return nextint++;
}

MIntVar* createIntVar(const string& name) {
	auto var = new MIntVar();
	var->var = nextint++;
	var->hasmap = false;
	var->hasvalue = false;
	name2int.insert({name, var});
	return var;
}

MBoolArrayVar* createBoolArrayVar(const string& name, int nbelem) {
	auto var = new MBoolArrayVar();
	var->nbelem = nbelem;
	name2boolarray.insert({name, var});
	return var;
}

MIntArrayVar* createIntArrayVar(const string& name, int nbelem) {
	auto var = new MIntArrayVar();
	var->nbelem = nbelem;
	name2intarray.insert({name, var});
	return var;
}

MBoolVar* FZ::getBoolVar(const string& name) {
	auto it = name2bool.find(name);
	if (it == name2bool.end()) {
		throw fzexception("Variable was not declared.\n");
	}
	return (*it).second;
}

MIntVar* FZ::getIntVar(const string& name) {
	auto it = name2int.find(name);
	if (it == name2int.end()) {
		throw fzexception("Variable was not declared.\n");
	}
	return (*it).second;
}

//IMPORTANT: index starts at ONE, so map to 0 based!
MBoolVar* FZ::getBoolVar(const string& name, int index) {
	auto it = name2boolarray.find(name);
	if (it == name2boolarray.end() || (*it).second->vars.size() < index) {
		throw fzexception("Array was not declared or not initialized.\n");
	}
	return (*it).second->vars[index - 1];
}

MIntVar* FZ::getIntVar(const string& name, int index) {
	auto it = name2intarray.find(name);
	if (it == name2intarray.end() || (*it).second->vars.size() < index) {
		throw fzexception("Array was not declared or not initialized.\n");
	}
	return (*it).second->vars[index - 1];
}

int FZ::getVar(const string& name, bool expectbool) {
	if (expectbool) {
		return getBoolVar(name)->var;
	} else {
		return getIntVar(name)->var;
	}
}

int FZ::getVar(const string& name, int index, bool expectbool) {
	if (expectbool) {
		return getBoolVar(name, index)->var;
	} else {
		return getIntVar(name, index)->var;
	}
}

void Var::add(Storage& storage) {
	if (type != VAR_BOOL) {
		throw fzexception("Incorrect type.\n");
	}

	MBoolVar* var = createBoolVar(getName());
	if (expr != NULL) {
		storage.addBoolExpr(*var, *expr);
	}
}

void IntVar::add(Storage& storage) {
	if (type != VAR_INT) {
		throw fzexception("Incorrect type.\n");
	}

	auto var = createIntVar(getName());

	//values
	bool nobounds = true;
	if (enumvalues) {
		nobounds = false;
		var->range = false;
		var->values = *values;
	} else if (range) {
		nobounds = false;
		var->set(true, begin, end);
	} else if (expr == NULL) {
		throw fzexception("Unbounded integer types are not supported by the backend.\n");
	}

	if (expr != NULL) {
		storage.addIntExpr(*var, nobounds, *expr);
	}
	storage.writeIntVar(*var);
}

void ArrayVar::add(Storage& storage) {
	if (type != VAR_ARRAY) {
		throw fzexception("Incorrect type.\n");
	}

	VAR_TYPE mappedtype = rangetype;
	if (rangevar != NULL) {
		mappedtype = rangevar->type;
	}

	if (arraylit != NULL && arraylit->exprs->size() != 0) {
		if ((int) arraylit->exprs->size() != end) {
			throw fzexception("Incorrect nb of expressions.\n");
		}
	}

	if (mappedtype == VAR_BOOL) {
		auto var = createBoolArrayVar(getName(), end);
		for (int i = 1; i <= end; i++) {
			auto boolvar = new MBoolVar();
			boolvar->var = nextint++;
			boolvar->hasmap = false;
			boolvar->hasvalue = false;
			var->vars.push_back(boolvar);
		}
		// values
		if (arraylit != NULL) {
			int index = 1;
			for (auto i = arraylit->exprs->begin(); i < arraylit->exprs->end(); ++i, ++index) {
				storage.addBoolExpr(*var->vars[index], **i);
			}
		}
	} else {
		auto var = createIntArrayVar(getName(), end);

		auto intvar = new MIntVar();
		intvar->var = nextint++;
		intvar->hasmap = false;
		intvar->hasvalue = false;
		bool nobounds = true;
		if (rangevar != NULL) {
			auto rangedvar = dynamic_cast<IntVar*>(rangevar);
			if (rangedvar->enumvalues) {
				nobounds = false;
				intvar->range = false;
				intvar->values = *rangedvar->values;
			} else if (rangedvar->range) {
				nobounds = false;
				intvar->set(true, rangedvar->begin, rangedvar->end);
			}
		}

		for (int i = 1; i <= end; i++) {
			auto tempvar = new MIntVar(*intvar);
			intvar->var = nextint++;
			var->vars.push_back(tempvar);
		}

		// values
		if (arraylit != NULL) {
			int index = 0;
			for (auto i = arraylit->exprs->begin(); i < arraylit->exprs->end(); ++i, ++index) {
				storage.addIntExpr(*var->vars[index], nobounds, **i);
			}
		}

		for (auto i = var->vars.begin(); i < var->vars.end(); ++i) {
			storage.writeIntVar(**i);
		}
	}
}

int FZ::parseBool(Storage& storage, const Expression& expr) {
	if (expr.type == EXPR_BOOL) {
		return (expr.boollit ? storage.getTrue() : storage.getFalse());
	} else if (expr.type == EXPR_ARRAYACCESS) {
		return getVar(*expr.arrayaccesslit->id, expr.arrayaccesslit->index, true);
	} else if (expr.type == EXPR_IDENT) {
		return getVar(*expr.ident->name, true);
	} else {
		throw fzexception("Unexpected type.\n");
	}
}

int FZ::parseInt(Storage& storage, const Expression& expr) {
	if (expr.type == EXPR_INT) {
		return storage.addCPVar(expr.intlit, expr.intlit);
	} else if (expr.type == EXPR_ARRAYACCESS) {
		return getVar(*expr.arrayaccesslit->id, expr.arrayaccesslit->index, false);
	} else if (expr.type == EXPR_IDENT) {
		return getVar(*expr.ident->name, false);
	} else {
		throw fzexception("Unexpected type.\n");
	}
}

int FZ::parseParInt(Storage& storage, const Expression& expr) {
	if (expr.type == EXPR_INT) {
		return expr.intlit;
	} else if (expr.type == EXPR_ARRAYACCESS) {
		return getVar(*expr.arrayaccesslit->id, expr.arrayaccesslit->index, false);
	} else if (expr.type == EXPR_IDENT) {
		return getVar(*expr.ident->name, false);
	} else {
		throw fzexception("Unexpected type.\n");
	}
}

std::vector<int> FZ::parseArray(Storage& storage, VAR_TYPE type, Expression& expr) {
	if (expr.type != EXPR_ARRAY) {
		throw fzexception("Unexpected type.\n");
	}

	std::vector<int> elems;
	for (auto i = expr.arraylit->exprs->begin(); i < expr.arraylit->exprs->end(); ++i) {
		if (type == VAR_BOOL) {
			elems.push_back(parseBool(storage, **i));
		} else {
			elems.push_back(parseInt(storage, **i));
		}
	}
	return elems;
}

std::vector<int> FZ::parseParIntArray(Storage& storage, Expression& expr) {
	if (expr.type != EXPR_ARRAY) {
		throw fzexception("Unexpected type.\n");
	}

	std::vector<int> elems;
	for (auto i = expr.arraylit->exprs->begin(); i < expr.arraylit->exprs->end(); ++i) {
		elems.push_back(parseParInt(storage, **i));
	}
	return elems;
}
