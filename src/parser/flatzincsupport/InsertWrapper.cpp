/*
 * Copyright 2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#include "InsertWrapper.hpp"

#include <cassert>
#include <string>
#include <iostream>
#include <algorithm>

#include "FZDatastructs.hpp"
#include "Storage.hpp"
#include "fzexception.hpp"
#include "utils/StringUtils.hpp"

using namespace std;
using namespace FZ;

InsertWrapper::InsertWrapper(MinisatID::ExternalConstraintVisitor* store)
		: storage(new Storage(store)) {
	name2type["bool2int"] = bool2int;
	name2type["bool_and"] = booland;
	name2type["bool_clause"] = boolclause;
	name2type["bool_eq"] = booleq;
	name2type["bool_eq_reif"] = booleqr;
	name2type["bool_le"] = boolle;
	name2type["bool_le_reif"] = booller;
	name2type["bool_lt"] = boollt;
	name2type["bool_lt_reif"] = boolltr;
	name2type["bool_not"] = boolnot;
	name2type["bool_or"] = boolor;
	name2type["bool_xor"] = boolxor;

	name2type["int_abs"] = intabs;
	name2type["int_div"] = intdiv;
	name2type["int_eq"] = inteq;
	name2type["int_eq_reif"] = inteqr;
	name2type["int_le"] = intle;
	name2type["int_le_reif"] = intler;
	name2type["int_lt"] = intlt;
	name2type["int_lt_reif"] = intltr;
	name2type["int_max"] = intmax;
	name2type["int_min"] = intmin;
	name2type["int_mod"] = intmod;
	name2type["int_ne"] = intne;
	name2type["int_ne_reif"] = intner;
	name2type["int_plus"] = intplus;
	name2type["int_times"] = inttimes;
	name2type["int_lin_eq"] = intlineq;
	name2type["int_lin_eq_reif"] = intlineqr;
	name2type["int_lin_le"] = intlinle;
	name2type["int_lin_le_reif"] = intlinler;
	name2type["int_lin_ne"] = intlinne;
	name2type["int_lin_ne_reif"] = intlinner;

	name2type["array_bool_and"] = arraybooland;
	name2type["array_bool_or"] = arrayboolor;
	name2type["array_bool_xor"] = arrayboolxor;
	name2type["array_bool_element"] = arrayboolelem;
	name2type["array_int_element"] = arrayintelem;
	name2type["array_var_bool_element"] = arrayvarboolelem;
	name2type["array_var_int_element"] = arrayvarintelem;

	name2type["set_in"] = setin;
	name2type["set_in_reif"] = setinr;
}

InsertWrapper::~InsertWrapper() {
	delete (storage);
}

bool InsertWrapper::isCertainlyUnsat() const {
	return storage->isCertainlyUnsat();
}

void InsertWrapper::add(Var* var) {
	for (auto expr : *var->id->arguments) {
		if (expr->type != EXPR_TYPE::EXPR_IDENT) {
			continue;
		}
		auto ident = expr->ident;
		if ((*ident->name) == "output_var") {
			var->setOutput();
		} else if ((*ident->name) == "output_array") {
			MAssert(ident->arguments->size()==1);
			MAssert((*ident->arguments)[0]->type==EXPR_TYPE::EXPR_ARRAY);
			const auto& ranges = *(*ident->arguments)[0]->arraylit->exprs;

			var->setOutput();

			stringstream ss;
			ss << var->getName() << " = array" << ranges.size() << "d(";
			bool begin = true;
			for (auto it = ranges.rbegin(); it != ranges.rend(); ++it) {
				if (not begin) {
					ss << ",";
				}
				begin = false;
				MAssert((*it)->type==EXPR_TYPE::EXPR_SET);
				MAssert((*it)->setlit->range);
				ss << (*it)->setlit->begin << ".." << (*it)->setlit->end;
			}
			var->setOutputName(ss.str());
		}
	}
	var->add(*storage);
}

void InsertWrapper::parseArgs(const vector<Expression*>& origargs, vector<int>& args, const vector<ARG_TYPE>& expectedtypes) {
	if (origargs.size() != expectedtypes.size()) {
		throw fzexception("Incorrect number of arguments.\n");
	}
	unsigned int itype = 0;
	for (auto i = origargs.rbegin(); i < origargs.rend(); ++i, ++itype) {
		auto expectedtype = expectedtypes[itype];
		auto& expr = **i;
		switch (expectedtype) {
		case ARG_BOOL:
			args.push_back(parseBool(*storage, expr));
			break;
		case ARG_INT:
			args.push_back(parseInt(*storage, expr));
			break;
		default:
			throw fzexception("Unexpected type in parsing arguments.\n");
		}
	}
}

bool hasDefinitionAnnotation(const vector<Expression*>& args, int& definitionid) {
	bool defined = false;
	for (auto i = args.begin(); i < args.end(); ++i) {
		if ((*i)->type == EXPR_IDENT && (*i)->ident->name->compare("inductivelydefined") == 0) {
			if ((*i)->ident->arguments != NULL) {
				if ((*i)->ident->arguments->size() == 1 && (*(*i)->ident->arguments->begin())->type == EXPR_INT) {
					definitionid = (*(*i)->ident->arguments->begin())->intlit;
				} else {
					throw fzexception("Incorrect number of annotation arguments");
				}
			} else {
				definitionid = 1;
			}
			defined = true;
		}
	}
	return defined;
}

template<class T>
T getRevArg(const vector<T>& list, int index) {
	return list[list.size() - index - 1];
}

int getMax(const MIntVar& var) {
	if (var.range) {
		return var.end;
	} else {
		auto m = var.values.front();
		for (auto value : var.values) {
			m = max(m, value);
		}
		return m;
	}
}

int getMin(const MIntVar& var) {
	if (var.range) {
		return var.begin;
	} else {
		auto m = var.values.front();
		for (auto value : var.values) {
			m = min(m, value);
		}
		return m;
	}
}

int getMinProd(int min1, int min2, int max1, int max2){
	auto m = min(min1*min2, max1*max2);
	m = min(m, min2*max1);
	return min(m, min1*max2);
}

int getMaxProd(int min1, int min2, int max1, int max2){
	auto m = max(min1*min2, max1*max2);
	m = max(m, min2*max1);
	return max(m, min1*max2);
}

uint getPos(int x) {
	if (x < 0) {
		throw idpexception("A variable ID cannot be negative");
	}
	return uint(x);
}

void createAbs(uint varx, uint varabsx, Storage* storage){
	auto tseitin = storage->createOneShotLit();
	auto tseitin1 = storage->createOneShotLit();
	auto tseitin2 = storage->createOneShotLit();
	storage->addBinI(tseitin, varx, MinisatID::EqType::L, 0);
	storage->addProduct(tseitin1, { getPos(varx) }, 1, MinisatID::EqType::EQ, varabsx);
	storage->addProduct(tseitin2, { getPos(varx) }, -1, MinisatID::EqType::EQ, varabsx);
	storage->addClause( { tseitin2 }, { tseitin });
	storage->addClause( { tseitin1, tseitin }, { });
}

/**
 * x/y=z with rounding down
 *
 * x/y-c = z with c [0,1)
 *
 * x = (z+c)*y
 * x = z*y + c*y
 * x = z*y + d with d [0,y)
 * 			and condition on d: (x-d) multiple of y or there is some e such that (x-d)=y*e without rounding
 *
 * x-d = z*y
 */

void createDiv(uint varx, uint vary, uint varz, Storage* storage){
	auto x = storage->getCPVar(varx);
	auto y = storage->getCPVar(vary);
	auto z = storage->getCPVar(varz);
	auto absmaxy = max(abs(getMax(y)), abs(getMin(y)));
	auto c = storage->addCPVar(0, absmaxy);
	auto absy = storage->addCPVar(0, absmaxy);
	createAbs(y.var, absy, storage);
	storage->addBinT(storage->getTrue(), c, EqType::L, absy);
	storage->addBinI(storage->getTrue(), vary, EqType::NEQ, 0);

	auto miny = getMin(y);
	auto minz = getMin(z);
	auto maxy = getMax(y);
	auto maxz = getMax(z);
	auto prodyz = storage->addCPVar(getMinProd(miny, minz, maxy, maxz), getMaxProd(miny, minz, maxy, maxz));
	storage->addProduct(storage->getTrue(), { y.var,z.var }, 1, MinisatID::EqType::EQ, prodyz);

	auto negx = storage->createOneShotLit();
	auto poslin = storage->createOneShotLit();
	auto neglin = storage->createOneShotLit();
	storage->addClause({neglin},{negx});
	storage->addClause({poslin,negx},{});
	storage->addBinI(negx, x.var, EqType::L, 0);
	storage->addLinear(poslin, {x.var, c, prodyz}, {1,-1,-1}, EqType::EQ, 0);
	storage->addLinear(neglin, {x.var, c, prodyz}, {1,1,-1}, EqType::EQ, 0);
}

void addReifSet(int head, uint var, bool range, int start, int end, const std::vector<int>& values, Storage* storage){
	if (range) {
		auto b1 = storage->createOneShotLit();
		storage->addBinI(b1, var, EqType::GEQ, start);
		auto b2 = storage->createOneShotLit();
		storage->addBinI(b2, var, EqType::LEQ, end);
		storage->writeEquiv(head, {b1,b2}, true);
	} else {
		std::vector<int> boolvars;
		for (auto j : values) {
			auto b = storage->createOneShotLit();
			boolvars.push_back(b);
			storage->addBinI(b, var, EqType::EQ, j);
		}
		storage->writeEquiv(head, boolvars, false);
	}
}

//VERY IMPORTANT: ALL PARSED VECTORS ARE REVERSED ORDER (TO HAVE FASTER PARSING)!!!!
void InsertWrapper::add(Constraint* var) {
	const auto& arguments = *var->id->arguments;
	vector<int> args;

	auto it = name2type.find(*var->id->name);

	if (it == name2type.end()) {
		stringstream ss;
		ss << "Constraint " << *var->id->name << " is not a supported constraint.\n";
		throw fzexception(ss.str());
	}

	switch ((*it).second) {
	case bool2int: {
		parseArgs(arguments, args, { ARG_BOOL, ARG_INT });
		//auto reiftrue = storage->createOneShotLit();
		//auto reiffalse = storage->createOneShotLit();
		//storage->addBinI(reiftrue, args[1], MinisatID::EqType::EQ, 1);
		//storage->addBinI(reiffalse, args[1], MinisatID::EqType::EQ, 0);
		//storage->addClause( { reiftrue }, { args[0] });
		//storage->addClause( { args[0], reiffalse }, { });
		storage->addBinI(-args[0], args[1], MinisatID::EqType::EQ, 0);
    storage->addBinI(args[0], args[1], MinisatID::EqType::EQ, 1);
		break;
	}
	case booland: {
		parseArgs(arguments, args, { ARG_BOOL, ARG_BOOL, ARG_BOOL });
		storage->writeEquiv(args[2], { args[0], args[1] }, true);
		break;
	}
	case boolclause: {
		if (arguments.size() != 2) {
			throw fzexception("Incorrect number of arguments.\n");
		}
		auto arg1 = parseBoolArray(*storage, *getRevArg(arguments, 0));
		auto arg2 = parseBoolArray(*storage, *getRevArg(arguments, 1));
		storage->addClause(arg1, arg2);
		break;
	}
	case arraybooland: {
		if (arguments.size() != 2) {
			throw fzexception("Incorrect number of arguments.\n");
		}
		auto arg1 = parseBoolArray(*storage, *getRevArg(arguments, 0));
		auto arg2 = parseBool(*storage, *getRevArg(arguments, 1));
		storage->writeEquiv(arg2, arg1, true);
		break;
	}
	case arrayboolor: {
		if (arguments.size() != 2) {
			throw fzexception("Incorrect number of arguments.\n");
		}
		auto arg1 = parseBoolArray(*storage, *getRevArg(arguments, 0));
		int arg2 = parseBool(*storage, *getRevArg(arguments, 1));
		storage->writeEquiv(arg2, arg1, false);
		break;
	}
	case arrayboolxor: {
		// The number of true elements should be ODD
		if (arguments.size() != 1) {
			throw fzexception("Incorrect number of arguments.\n");
		}
		auto arg1 = parseBoolArray(*storage, *getRevArg(arguments, 0));
		std::vector<uint> intargs;
		std::vector<int> weights;
		for (auto b : arg1) {
			auto i = storage->addCPVar(0, 1);
			intargs.push_back(i);
			weights.push_back(1);
			storage->addBinI(b, i, EqType::EQ, 1);
		}
		auto eq = storage->addCPVar(0, intargs.size());
		auto div = storage->addCPVar(0, intargs.size() / 2 + 1);
		intargs.push_back(eq);
		weights.push_back(-1);
		storage->addLinear(storage->getTrue(), intargs, weights, MinisatID::EqType::EQ, 0);
		storage->addLinear(storage->getTrue(), { div, eq }, { 2, -1 }, MinisatID::EqType::EQ, -1);
		break;
	}
	case arrayintelem: {
		if (arguments.size() != 3) {
			throw fzexception("Incorrect number of arguments.\n");
		}
		auto arg1 = parseInt(*storage, *getRevArg(arguments, 0));
		auto arg2 = parseParIntArray(*storage, *getRevArg(arguments, 1));
		auto arg3 = parseInt(*storage, *getRevArg(arguments, 2));
		for (uint counter = 0; counter < arg2.size(); ++counter) {
			auto reif = storage->createOneShotLit();
			auto reif2 = storage->createOneShotLit();
			storage->addBinI(reif, arg1, EqType::EQ, counter + 1);
			storage->addBinI(reif2, arg3, EqType::EQ, arg2[counter]);
			storage->addClause( { reif2 }, { reif });
		}
		storage->addBinI(storage->getTrue(), arg1, EqType::GEQ, 1);
		storage->addBinI(storage->getTrue(), arg1, EqType::LEQ, arg2.size());
		break;
	}
	case arrayvarintelem: {
		if (arguments.size() != 3) {
			throw fzexception("Incorrect number of arguments.\n");
		}
		auto arg1 = parseInt(*storage, *getRevArg(arguments, 0));
		auto arg2 = parseIntArray(*storage, *getRevArg(arguments, 1));
		auto arg3 = parseInt(*storage, *getRevArg(arguments, 2));
		for (uint counter = 0; counter < arg2.size(); ++counter) {
			auto reif = storage->createOneShotLit();
			auto reif2 = storage->createOneShotLit();
			storage->addBinI(reif, arg1, EqType::EQ, counter + 1);
			storage->addBinT(reif2, arg3, EqType::EQ, arg2[counter]);
			storage->addClause( { reif2 }, { reif });
		}
		storage->addBinI(storage->getTrue(), arg1, EqType::GEQ, 1);
		storage->addBinI(storage->getTrue(), arg1, EqType::LEQ, arg2.size());
		break;
	}
	case arrayvarboolelem: {
		if (arguments.size() != 3) {
			throw fzexception("Incorrect number of arguments.\n");
		}
		auto arg1 = parseInt(*storage, *getRevArg(arguments, 0));
		auto arg2 = parseBoolArray(*storage, *getRevArg(arguments, 1));
		auto arg3 = parseBool(*storage, *getRevArg(arguments, 2));
		for (uint counter = 0; counter < arg2.size(); ++counter) {
			auto reif = storage->createOneShotLit();
			storage->addBinI(reif, arg1, EqType::EQ, counter + 1);
			storage->addClause( { arg3 }, { reif, arg2[counter] });
			storage->addClause( { arg2[counter] }, { reif, arg3 });
		}
		storage->addBinI(storage->getTrue(), arg1, EqType::GEQ, 1);
		storage->addBinI(storage->getTrue(), arg1, EqType::LEQ, arg2.size());
		break;
	}
	case arrayboolelem: {
		if (arguments.size() != 3) {
			throw fzexception("Incorrect number of arguments.\n");
		}
		auto arg1 = parseInt(*storage, *getRevArg(arguments, 0));
		auto arg2 = parseParBoolArray(*storage, *getRevArg(arguments, 1));
		auto arg3 = parseBool(*storage, *getRevArg(arguments, 2));
		for (uint counter = 0; counter < arg2.size(); ++counter) {
			auto reif = storage->createOneShotLit();
			storage->addBinI(reif, arg1, EqType::EQ, counter + 1);
			if (arg2[counter]) {
				storage->addClause( { arg3 }, { reif });
			} else {
				storage->addClause( { }, { reif, arg3 });
			}
		}
		storage->addBinI(storage->getTrue(), arg1, EqType::GEQ, 1);
		storage->addBinI(storage->getTrue(), arg1, EqType::LEQ, arg2.size());
		break;
	}
	case setin: {
		if (arguments.size() != 2) {
			throw fzexception("Incorrect number of arguments.\n");
		}
		auto arg1 = parseInt(*storage, *getRevArg(arguments, 0));
		const auto& setarg = *getRevArg(arguments, 1);
		if (setarg.type == EXPR_TYPE::EXPR_SET) {
			int start = 0, end=0;
			std::vector<int> values;
			if (isRangeSet(setarg)) {
				auto beginend = parseParRangeSet(setarg);
				start = beginend.first;
				end = beginend.second;
			} else {
				values = parseParValueSet(*storage, setarg);
			}
			addReifSet(storage->getTrue(), arg1, isRangeSet(setarg), start, end, values, storage);
		} else if (setarg.type == EXPR_TYPE::EXPR_IDENT) {
			auto setvar = parseSet(*storage, *setarg.ident);
			addReifSet(storage->getTrue(), arg1, setvar->isrange, setvar->start, setvar->end, setvar->values, storage);
		} else if (setarg.type == EXPR_TYPE::EXPR_ARRAYACCESS) {
			auto setvar = storage->getSetVar(*setarg.arrayaccesslit->id, setarg.arrayaccesslit->index);
			addReifSet(storage->getTrue(), arg1, setvar->isrange, setvar->start, setvar->end, setvar->values, storage);
		} else {
			throw fzexception("Incorrect type, set or setliteral expected");
		}
		break;
	}
	case setinr: {
		if (arguments.size() != 3) {
			throw fzexception("Incorrect number of arguments.\n");
		}
		auto arg1 = parseInt(*storage, *getRevArg(arguments, 0));
		const auto& setarg = *getRevArg(arguments, 1);
		auto head = parseBool(*storage, *getRevArg(arguments, 2));
		if (setarg.type == EXPR_TYPE::EXPR_SET) {
			int start = 0, end=0;
			std::vector<int> values;
			if (isRangeSet(setarg)) {
				auto beginend = parseParRangeSet(setarg);
				start = beginend.first;
				end = beginend.second;
			} else {
				values = parseParValueSet(*storage, setarg);
			}
			addReifSet(head, arg1, isRangeSet(setarg), start, end, values, storage);
		} else if (setarg.type == EXPR_TYPE::EXPR_IDENT) {
			auto setvar = parseSet(*storage, *setarg.ident);
			addReifSet(head, arg1, setvar->isrange, setvar->start, setvar->end, setvar->values, storage);
		} else {
			throw fzexception("Incorrect type, set or setliteral expected");
		}
		break;
	}
	case booleq: {
		parseArgs(arguments, args, { ARG_BOOL, ARG_BOOL });
		storage->writeEquiv(args[0], { args[1] }, true);
		break;
	}
	case booleqr: {
		parseArgs(arguments, args, { ARG_BOOL, ARG_BOOL, ARG_BOOL });
		auto bothtruereif = storage->createOneShotLit();
		auto bothfalsereif = storage->createOneShotLit();
		storage->writeEquiv(bothtruereif, { args[0], args[1] }, true);
		storage->writeEquiv(bothfalsereif, { -args[0], -args[1] }, true);
		storage->writeEquiv(args[2], { bothfalsereif, bothtruereif }, false);
		break;
	}
	case boolle: {
		parseArgs(arguments, args, { ARG_BOOL, ARG_BOOL });
		storage->addClause( { args[1] }, { args[0] });
		break;
	}
	case booller: {
		parseArgs(arguments, args, { ARG_BOOL, ARG_BOOL, ARG_BOOL });
		storage->writeEquiv(args[2], { -args[0], args[1] }, false);
		break;
	}
	case boollt: {
		parseArgs(arguments, args, { ARG_BOOL, ARG_BOOL });
		storage->addClause( { }, { args[0] });
		storage->addClause( { args[1] }, { });
		break;
	}
	case boolltr: {
		parseArgs(arguments, args, { ARG_BOOL, ARG_BOOL, ARG_BOOL });
		storage->writeEquiv(args[2], { -args[0], args[1] }, true);
		break;
	}
	case boolnot: {
		parseArgs(arguments, args, { ARG_BOOL, ARG_BOOL });
		storage->writeEquiv(args[1], { -args[0] }, true);
		break;
	}
	case boolor: {
		parseArgs(arguments, args, { ARG_BOOL, ARG_BOOL, ARG_BOOL });
		storage->writeEquiv(args[2], { args[0], args[1] }, false);
		break;
	}
	case boolxor: {
		parseArgs(arguments, args, { ARG_BOOL, ARG_BOOL, ARG_BOOL });
		auto firstfalsereif = storage->createOneShotLit();
		auto secondfalsereif = storage->createOneShotLit();
		storage->writeEquiv(firstfalsereif, { -args[0], args[1] }, true);
		storage->writeEquiv(secondfalsereif, { args[0], -args[1] }, true);
		storage->writeEquiv(args[2], { firstfalsereif, secondfalsereif }, false);
		break;
	}
	case inteq: {
		parseArgs(arguments, args, { ARG_INT, ARG_INT });
		storage->addBinT(storage->getTrue(), args[0], MinisatID::EqType::EQ, args[1]);
		break;
	}
	case inteqr: {
		parseArgs(arguments, args, { ARG_INT, ARG_INT, ARG_BOOL });
		storage->addBinT(args[2], args[0], MinisatID::EqType::EQ, args[1]);
		break;
	}
	case intle: {
		parseArgs(arguments, args, { ARG_INT, ARG_INT });
		storage->addBinT(storage->getTrue(), args[0], MinisatID::EqType::LEQ, args[1]);
		break;
	}
	case intler: {
		parseArgs(arguments, args, { ARG_INT, ARG_INT, ARG_BOOL });
		storage->addBinT(args[2], args[0], MinisatID::EqType::LEQ, args[1]);
		break;
	}
	case intlt: {
		parseArgs(arguments, args, { ARG_INT, ARG_INT });
		storage->addBinT(storage->getTrue(), args[0], MinisatID::EqType::L, args[1]);
		break;
	}
	case intltr: {
		parseArgs(arguments, args, { ARG_INT, ARG_INT, ARG_BOOL });
		storage->addBinT(args[2], args[0], MinisatID::EqType::L, args[1]);
		break;
	}
	case intne: {
		parseArgs(arguments, args, { ARG_INT, ARG_INT });
		storage->addBinT(storage->getTrue(), args[0], MinisatID::EqType::NEQ, args[1]);
		break;
	}
	case intner: {
		parseArgs(arguments, args, { ARG_INT, ARG_INT, ARG_BOOL });
		storage->addBinT(args[2], args[0], MinisatID::EqType::NEQ, args[1]);
		break;
	}
	case intabs: {
		// abs(x0)=x1
		parseArgs(arguments, args, { ARG_INT, ARG_INT });
		createAbs(args[0], args[1], storage);
		break;
	}
	case intdiv: {
		// x / y = z
		parseArgs(arguments, args, { ARG_INT, ARG_INT, ARG_INT });
		createDiv(args[0], args[1], args[2], storage);
		break;
	}
	case intmax: {
		parseArgs(arguments, args, { ARG_INT, ARG_INT, ARG_INT });
		auto tseitin = storage->createOneShotLit();
		auto tseitin1 = storage->createOneShotLit();
		auto tseitin2 = storage->createOneShotLit();
		storage->addClause( { tseitin2 }, { tseitin });
		storage->addClause( { tseitin1, tseitin }, { });
		storage->addBinT(tseitin, args[0], MinisatID::EqType::L, args[1]);
		storage->addBinT(tseitin1, args[0], MinisatID::EqType::EQ, args[2]);
		storage->addBinT(tseitin2, args[1], MinisatID::EqType::EQ, args[2]);
		break;
	}
	case intmin: {
		parseArgs(arguments, args, { ARG_INT, ARG_INT, ARG_INT });
		auto tseitin = storage->createOneShotLit();
		auto tseitin1 = storage->createOneShotLit();
		auto tseitin2 = storage->createOneShotLit();
		storage->addClause( { tseitin1 }, { tseitin });
		storage->addClause( { tseitin2, tseitin }, { });
		storage->addBinT(tseitin, args[0], MinisatID::EqType::L, args[1]);
		storage->addBinT(tseitin1, args[0], MinisatID::EqType::EQ, args[2]);
		storage->addBinT(tseitin2, args[1], MinisatID::EqType::EQ, args[2]);
		break;
	}
	case intmod: {
		// x mod y = z
		parseArgs(arguments, args, { ARG_INT, ARG_INT, ARG_INT });
		// x - trunc(x/y)*y = z
		auto x = storage->getCPVar(args[0]);
		auto absmaxx = max(abs(getMin(x)), abs(getMax(x)));
		auto div = storage->addCPVar(-absmaxx,absmaxx);
		createDiv(args[0], args[1], div, storage);
		auto prod = storage->addCPVar(-absmaxx,absmaxx);
		storage->addProduct(storage->getTrue(), { (uint)args[1], div }, 1, MinisatID::EqType::EQ, prod);
		storage->addLinear(storage->getTrue(), { x.var, prod, (uint)args[2] }, { 1, -1, -1 }, MinisatID::EqType::EQ, 0);
		break;
	}
	case intplus: {
		parseArgs(arguments, args, { ARG_INT, ARG_INT, ARG_INT });
		storage->addLinear(storage->getTrue(), { getPos(args[0]), getPos(args[1]), getPos(args[2]) }, { 1, 1, -1 }, MinisatID::EqType::EQ, 0);
		break;
	}
	case inttimes: {
		parseArgs(arguments, args, { ARG_INT, ARG_INT, ARG_INT });
		storage->addProduct(storage->getTrue(), { getPos(args[0]), getPos(args[1]) }, 1, MinisatID::EqType::EQ, args[2]);
		break;
	}
	case intlineq: {
		storage->addLinear(arguments, MinisatID::EqType::EQ, false);
		break;
	}
	case intlineqr: {
		storage->addLinear(arguments, MinisatID::EqType::EQ, true);
		break;
	}
	case intlinle: {
		storage->addLinear(arguments, MinisatID::EqType::LEQ, false);
		break;
	}
	case intlinler: {
		storage->addLinear(arguments, MinisatID::EqType::LEQ, true);
		break;
	}
	case intlinne: {
		storage->addLinear(arguments, MinisatID::EqType::NEQ, false);
		break;
	}
	case intlinner: {
		storage->addLinear(arguments, MinisatID::EqType::NEQ, true);
		break;
	}
	default:
		stringstream ss;
		ss << "Constraint " << *var->id->name << " is not a supported constraint.\n";
		throw fzexception(ss.str());
	}
}

MIntVar* InsertWrapper::createNegation(const MIntVar& var) {
	auto newvar = new MIntVar();
	newvar->var = storage->createOneShotVar();
	if (var.range) {
		newvar->range = true;
		newvar->begin = -var.end;
		newvar->end = -var.begin;
	} else {
		newvar->range = false;
		for (auto v : var.values) {
			newvar->values.push_back(-v);
		}
	}
	storage->writeIntVar(*newvar);
	storage->addLinear(storage->getTrue(), { var.var, newvar->var }, { 1, 1 }, MinisatID::EqType::EQ, 0);
	return newvar;
}

void InsertWrapper::addOptim(Expression& expr, bool maxim) {
	MIntVar* var;
	if (expr.type == EXPR_ARRAYACCESS) {
		var = storage->getIntVar(*expr.arrayaccesslit->id, expr.arrayaccesslit->index);
	} else if (expr.type == EXPR_IDENT) {
		var = storage->getIntVar(*expr.ident->name);
	} else {
		throw fzexception("Unexpected type in adding optimization statement.\n");
	}

	storage->addOptim(*var, not maxim);
}

void InsertWrapper::add(Search* search) {
	switch (search->type) {
	case SOLVE_SATISFY:
		break;
	case SOLVE_MINIMIZE:
		addOptim(*search->expr, false);
		break;
	case SOLVE_MAXIMIZE:
		addOptim(*search->expr, true);
		break;
	}
}
