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
#include <iostream>

#include "Storage.hpp"
#include "fzexception.hpp"

using namespace std;
using namespace FZ;

std::ostream& FZ::operator<<(std::ostream& stream, EXPR_TYPE type){
	switch(type){
	case EXPR_TYPE::EXPR_ARRAY:
		stream <<"array";
		break;
	case EXPR_TYPE::EXPR_ARRAYACCESS:
		stream <<"arrayaccess";
		break;
	case EXPR_TYPE::EXPR_BOOL:
		stream <<"bool";
		break;
	case EXPR_TYPE::EXPR_FLOAT:
		stream <<"float";
		break;
	case EXPR_TYPE::EXPR_IDENT:
		stream <<"identifier";
		break;
	case EXPR_TYPE::EXPR_INT:
		stream <<"int";
		break;
	case EXPR_TYPE::EXPR_SET:
		stream <<"set";
		break;
	case EXPR_TYPE::EXPR_STRING:
		stream <<"string";
		break;
	}
	return stream;
}

bool MBoolVar::getValue() const {
	MAssert(hasValue());
	if (hasvalue) {
		return value;
	} else {
		return mappedvar->getValue();
	}
}

int MIntVar::getValue() const {
	MAssert(hasValue());
	if (hasvalue) {
		return value;
	} else {
		return mappedvar->getValue();
	}
}

void FZ::Var::add(Storage& storage) {
	if (type != VAR_BOOL) {
		throw fzexception("Incorrect type.\n");
	}

	auto var = storage.createBoolVar(getName(), isOutput());
	if (expr != NULL) {
		storage.addBoolExpr(*var, *expr);
	}
}

void IntVar::add(Storage& storage) {
	if (type != VAR_INT) {
		throw fzexception("Incorrect type.\n");
	}

	auto var = storage.createIntVar(getName(), isOutput());

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
		nobounds = false;
		var->set(true, getMinElem<int>(), getMaxElem<int>());
	}

	if (expr != NULL) {
		storage.addIntExpr(*var, nobounds, *expr);
	}
	storage.writeIntVar(*var);
	if (expr != NULL) {
		if (var->hasvalue) {
			storage.addBinI(storage.getTrue(), var->var, EqType::EQ, var->value);
		} else {
			storage.addBinT(storage.getTrue(), var->var, EqType::EQ, var->mappedvar->var);
		}
	}
}

void SetVar::add(Storage& storage) {
	//cerr <<"Adding set " <<getName() <<"\n";
	if (expr == NULL) {
		throw fzexception("Only par sets are currently allowed.");
	}
	if (expr->type == EXPR_SET) {
		auto setlit = expr->setlit;
		isrange = setlit->range;
		if (setlit->range) {
			start = setlit->begin;
			end = setlit->end;
		} else {
			setValues(parseParValueSet(storage, *expr));
		}
	} else if (expr->type == EXPR_IDENT) {
		auto setvar = storage.getSetVar(*expr->ident->name);
		isrange = setvar->isrange;
		start = setvar->start;
		end = setvar->end;
		setValues(setvar->values);
	} else {
		throw fzexception("Invalid type");
	}

	storage.notifySetVar(getName(), this);

	// Check with int specification
	bool unsat = false;
	if (var->range) {
		if (isrange) {
			if (start < var->begin || end > var->end) {
				unsat = true;
			}
		} else {
			for (auto v : getValues()) {
				if (v < var->begin || v > var->end) {
					unsat = true;
					break;
				}
			}
		}
	} else if (var->enumvalues) {
		if (isrange) {
			// FIXME what if the enumvalues contains duplicates?
			MAssert(end>=start);
			size_t diff = end-start;
			if (var->values->size() < diff) {
				unsat = true;
			}
			for (auto ev : *var->values) {
				if (ev < start || ev > end) {
					unsat = true;
					break;
				}
			}
		} else {
			for (auto v : getValues()) {
				bool found = false;
				for (auto ev : *var->values) {
					if (v == ev) {
						found = true;
						break;
					}
				}
				if (not found) {
					unsat = true;
					break;
				}
			}
		}
	}
	if (unsat) {
		storage.notifyUnsat();
	}
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
		//	cerr <<"Adding bool array " <<getName() <<"\n";
		auto var = storage.createBoolArrayVar(getName(), getOutputName(), end, isOutput());
		// values
		if (arraylit != NULL) {
			int index = 0;
			for (auto i = arraylit->exprs->rbegin(); i < arraylit->exprs->rend(); ++i, ++index) {
				storage.addBoolExpr(*var->vars[index], **i);
			}
		}
	} else if(mappedtype==VAR_INT){
		bool nobounds = false;
		//cerr <<"Adding int array " <<getName() <<"\n";
		auto var = storage.createIntArrayVar(getName(), getOutputName(), end, rangevar, nobounds, isOutput());
		// values
		if (arraylit != NULL) {
			int index = 0;
			for (auto i = arraylit->exprs->rbegin(); i < arraylit->exprs->rend(); ++i, ++index) {
				auto subvar = var->vars[index];
				storage.addIntExpr(*subvar, nobounds, **i);
				storage.writeIntVar(*subvar);
				if (subvar->hasvalue) {
					storage.addBinI(storage.getTrue(), subvar->var, EqType::EQ, subvar->value);
				} else {
					storage.addBinT(storage.getTrue(), subvar->var, EqType::EQ, subvar->mappedvar->var);
				}
			}
		} else {
			for (auto i = var->vars.cbegin(); i < var->vars.cend(); ++i) {
				storage.writeIntVar(**i);
			}
		}
	}else if(mappedtype ==VAR_SET){
		if(isOutput()){
			throw idpexception("Output sets are not supported");
		}
		auto var = storage.createSetArrayVar(getName(), getOutputName(), end);
		if (arraylit != NULL) {
			int index = 0;
			for (auto i = arraylit->exprs->rbegin(); i < arraylit->exprs->rend(); ++i, ++index) {
				storage.addSetExpr(*var->vars[index], **i);
			}
		}
	}else{
		throw idpexception("Unsupported array type");
	}
}

int FZ::parseBool(Storage& storage, const Expression& expr) {
	if (expr.type == EXPR_BOOL) {
		return (expr.boollit ? storage.getTrue() : storage.getFalse());
	} else if (expr.type == EXPR_ARRAYACCESS) {
		return storage.getBoolVar(*expr.arrayaccesslit->id, expr.arrayaccesslit->index)->var;
	} else if (expr.type == EXPR_IDENT) {
		return storage.getBoolVar(*expr.ident->name)->var;
	}
	stringstream ss;
	ss << "Unexpected type " << expr.type << " instead of " << EXPR_BOOL <<", " <<EXPR_ARRAYACCESS <<" or " <<EXPR_IDENT << ".\n";
	throw fzexception(ss.str());
}

bool FZ::parseParBool(Storage& storage, const Expression& expr) {
	if (expr.type == EXPR_BOOL) {
		return expr.boollit;
	} else if (expr.type == EXPR_ARRAYACCESS) {
		auto boolvar = storage.getBoolVar(*expr.arrayaccesslit->id, expr.arrayaccesslit->index);
		if (not boolvar->hasValue()) {
			throw fzexception("Expecting PAR bool");
		}
		return boolvar->getValue();
	} else if (expr.type == EXPR_IDENT) {
		auto boolvar = storage.getBoolVar(*expr.ident->name);
		if (not boolvar->hasValue()) {
			throw fzexception("Expecting PAR bool");
		}
		return boolvar->getValue();
	}
	stringstream ss;
	ss << "Unexpected type " << expr.type << " instead of " << EXPR_BOOL <<", " <<EXPR_ARRAYACCESS <<" or " <<EXPR_IDENT << ".\n";
	throw fzexception(ss.str());
}

int FZ::parseInt(Storage& storage, const Expression& expr) {
	if (expr.type == EXPR_INT) {
		return storage.addCPVar(expr.intlit, expr.intlit);
	} else if (expr.type == EXPR_ARRAYACCESS) {
		return storage.getIntVar(*expr.arrayaccesslit->id, expr.arrayaccesslit->index)->var;
	} else if (expr.type == EXPR_IDENT) {
		return storage.getIntVar(*expr.ident->name)->var;
	}
	stringstream ss;
	ss << "Unexpected type " << expr.type << " instead of " << EXPR_INT <<", " <<EXPR_ARRAYACCESS <<" or " <<EXPR_IDENT << ".\n";
	throw fzexception(ss.str());
}

MSetVar* FZ::parseSet(Storage& storage, const Identifier& ident) {
	return storage.getSetVar(*ident.name);
}

int FZ::parseParInt(Storage& storage, const Expression& expr) {
	if (expr.type == EXPR_INT) {
		return expr.intlit;
	} else if (expr.type == EXPR_ARRAYACCESS) {
		auto intvar = storage.getIntVar(*expr.arrayaccesslit->id, expr.arrayaccesslit->index);
		if (not intvar->hasValue()) {
			throw fzexception("Expecting PAR int");
		}
		return intvar->getValue();
	} else if (expr.type == EXPR_IDENT) {
		auto intvar = storage.getIntVar(*expr.ident->name);
		if (not intvar->hasValue()) {
			throw fzexception("Expecting PAR int");
		}
		return intvar->getValue();
	}
	stringstream ss;
	ss << "Unexpected type " << expr.type << " instead of " << EXPR_INT <<", " <<EXPR_ARRAYACCESS <<" or " <<EXPR_IDENT << ".\n";
	throw fzexception(ss.str());
}

bool FZ::isRangeSet(const Expression& expr) {
	return expr.type == EXPR_SET && expr.setlit->range;
}

std::pair<int, int> FZ::parseParRangeSet(const Expression& expr) {
	if (expr.type != EXPR_SET || not expr.setlit->range) {
		throw fzexception("Unexpected type in parseParRangeSet.\n");
	}

	return {expr.setlit->begin, expr.setlit->end};
}

void parseSetLit(std::vector<int>& elems, const Expression& expr, Storage& storage){
	if (expr.type != EXPR_SET || expr.setlit->range) {
		throw fzexception("Unexpected type in parsing Set Lit.\n");
	}
	for (auto i : *(expr.setlit->values)) {
		if((*i).type==EXPR_TYPE::EXPR_SET){
			auto sl = *(*i).setlit;
			if(sl.range){
				for(int j=sl.begin; j<=sl.end; ++j){
					elems.push_back(j);
				}
			}else{
				parseSetLit(elems, *i, storage);
			}
		}else{
			auto result = parseParInt(storage, *i);
			elems.push_back(result);
		}
	}
}

std::vector<int> FZ::parseParValueSet(Storage& storage, const Expression& expr) {
	std::vector<int> elems;
	parseSetLit(elems, expr, storage);
	return elems;
}

std::vector<int> FZ::parseParIntArray(Storage& storage, Expression& expr) {
	if (expr.type == EXPR_ARRAY) {
		std::vector<int> elems;
		for (auto i = expr.arraylit->exprs->rbegin(); i < expr.arraylit->exprs->rend(); ++i) {
			elems.push_back(parseParInt(storage, **i));
		}
		return elems;
	} else if (expr.type == EXPR_IDENT) {
		return storage.getParIntArrayValues(*expr.ident->name);
	}

	stringstream ss;
	ss << "Unexpected type " << expr.type << " instead of " << EXPR_ARRAY << ".\n";
	throw fzexception(ss.str());
}

std::vector<bool> FZ::parseParBoolArray(Storage& storage, Expression& expr) {
	if (expr.type == EXPR_ARRAY) {
		std::vector<bool> elems;
		for (auto i = expr.arraylit->exprs->rbegin(); i < expr.arraylit->exprs->rend(); ++i) {
			elems.push_back(parseParBool(storage, **i));
		}
		return elems;
	} else if (expr.type == EXPR_IDENT) {
		return storage.getParBoolArrayValues(*expr.ident->name);
	}

	stringstream ss;
	ss << "Unexpected type " << expr.type << " instead of " << EXPR_ARRAY << ".\n";
	throw fzexception(ss.str());
}

std::vector<int> FZ::parseBoolArray(Storage& storage, Expression& expr) {
	if (expr.type == EXPR_ARRAY) {
		std::vector<int> elems;
		for (auto i = expr.arraylit->exprs->rbegin(); i < expr.arraylit->exprs->rend(); ++i) {
			elems.push_back(parseBool(storage, **i));
		}
		return elems;
	} else if (expr.type == EXPR_IDENT) {
		return storage.getBoolArrayVars(*expr.ident->name);
	} else {
		throw fzexception("Unexpected type in parseBoolArray.\n");
	}
}

std::vector<uint> FZ::parseIntArray(Storage& storage, Expression& expr) {
	if (expr.type == EXPR_ARRAY) {
		std::vector<uint> elems;
		for (auto i = expr.arraylit->exprs->rbegin(); i < expr.arraylit->exprs->rend(); ++i) {
			elems.push_back(parseInt(storage, **i));
		}
		return elems;
	} else if (expr.type == EXPR_IDENT) {
		return storage.getIntArrayVars(*expr.ident->name);
	} else {
		throw fzexception("Unexpected type in parseIntArray.\n");
	}
}
