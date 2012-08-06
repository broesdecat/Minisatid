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
}

InsertWrapper::~InsertWrapper() {
	delete (storage);
}

bool InsertWrapper::isCertainlyUnsat() const {
	return storage->isCertainlyUnsat();
}

void InsertWrapper::start() {
	cout << "c Automated transformation from a flatzinc model into ECNF.\n";
	cout << "p ecnf\n";
}

void InsertWrapper::finish() {
	storage->print(cout);
}

void InsertWrapper::add(Var* var) {
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
			throw fzexception("Unexpected type.\n");
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
		auto arg1 = parseArray(*storage, VAR_BOOL, *getRevArg(arguments, 0));
		auto arg2 = parseArray(*storage, VAR_BOOL, *getRevArg(arguments, 1));
		storage->addClause(arg1, arg2);
		break;
	}
	case arraybooland: {
		if (arguments.size() != 2) {
			throw fzexception("Incorrect number of arguments.\n");
		}
		auto arg1 = parseArray(*storage, VAR_BOOL, *getRevArg(arguments, 0));
		auto arg2 = parseBool(*storage, *getRevArg(arguments, 1));
		storage->writeEquiv(arg2, arg1, true);
		break;
	}
	case arrayboolor: {
		if (arguments.size() != 2) {
			throw fzexception("Incorrect number of arguments.\n");
		}
		auto arg1 = parseArray(*storage, VAR_BOOL, *getRevArg(arguments, 0));
		int arg2 = parseBool(*storage, *getRevArg(arguments, 1));
		storage->writeEquiv(arg2, arg1, false);
		break;
	}
	case booleq: {
		parseArgs(arguments, args, { ARG_BOOL, ARG_BOOL });
		storage->writeEquiv(args[0], { args[1] }, true);
		break;
	}
	case booleqr: {
		parseArgs(arguments, args, { ARG_BOOL, ARG_BOOL, ARG_BOOL });
		int bothtruereif = createOneShotVar();
		int bothfalsereif = createOneShotVar();
		storage->writeEquiv(bothtruereif, { args[0], args[1] }, true);
		storage->writeEquiv(bothfalsereif, { -args[0], -args[1] }, true);
		storage->writeEquiv(args[2], { bothfalsereif, bothtruereif }, false);
		break;
	}
	case boolle: {
		parseArgs(arguments, args, { ARG_BOOL, ARG_BOOL });
		storage->addClause( { args[0], args[1] }, { });
		break;
	}
	case booller: {
		parseArgs(arguments, args, { ARG_BOOL, ARG_BOOL, ARG_BOOL });
		storage->writeEquiv(args[2], { -args[0], args[1] }, false);
		break;
	}
	case boollt: {
		parseArgs(arguments, args, { ARG_BOOL, ARG_BOOL });
		storage->addClause( { args[1] }, { args[0] });
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
		auto firstfalsereif = createOneShotVar();
		auto secondfalsereif = createOneShotVar();
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
		//TODO binary/ternary functions
		/*	case intabs: {
		 parseArgs(arguments, args, {ARG_INT,ARG_INT});
		 //theory <<tab() <<"abs(" <<args[0] <<")= " <<args[1] <<endst();
		 break;}
		 case intdiv: {
		 parseArgs(arguments, args, {ARG_INT,ARG_INT,ARG_INT});
		 //theory <<tab() <<args[0] <<" / " <<args[1] <<" = " <<args[2] <<endst();
		 break;}
		 case intmax: {
		 parseArgs(arguments, args, {ARG_INT,ARG_INT,ARG_INT});
		 //theory <<tab() <<"max(" <<args[0] <<", " <<args[1] <<")= " <<args[2]<<endst();
		 break;}
		 case intmin: {
		 parseArgs(arguments, args, {ARG_INT,ARG_INT,ARG_INT});
		 //theory <<tab() <<"min(" <<args[0] <<", " <<args[1] <<")= " <<args[2] <<endst();
		 break;}
		 case intmod: {
		 parseArgs(arguments, args, {ARG_INT,ARG_INT,ARG_INT});
		 //theory <<tab() <<args[0] <<" mod " <<args[1] <<" = " <<args[2] <<endst();
		 break;}*/
	case intplus: {
		parseArgs(arguments, args, {ARG_INT,ARG_INT,ARG_INT});
		storage->addLinear(storage->getTrue(), {args[0], args[1], args[2]}, {1,1,-1}, MinisatID::EqType::EQ, 0);
		break;
	}
	case inttimes: {
		parseArgs(arguments, args, {ARG_INT,ARG_INT,ARG_INT});
		// FIXME addLinear(getProduct(), {args[0], args[1]}, args[2]);
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

MIntVar* InsertWrapper::createNegation(const MIntVar& var){
	auto newvar = new MIntVar();
	if(var.range){
		newvar->range = true;
		newvar->begin = -var.end;
		newvar->end = -var.begin;
	}else{
		newvar->range = false;
		for(auto v:var.values){
			newvar->values.push_back(-v);
		}
	}
	newvar->var = createOneShotVar();
	storage->writeIntVar(var);
	storage->addLinear(storage->getTrue(), {var.var, newvar->var}, {1,-1}, MinisatID::EqType::EQ, 0);
	return newvar;
}

void InsertWrapper::addOptim(Expression& expr, bool maxim) {
	MIntVar* var;
	if (expr.type == EXPR_ARRAYACCESS) {
		var = getIntVar(*expr.arrayaccesslit->id, expr.arrayaccesslit->index);
	} else if (expr.type == EXPR_IDENT) {
		var = getIntVar(*expr.ident->name);
	} else {
		throw fzexception("Unexpected type.\n");
	}

	if (maxim) {
		auto newvar = createNegation(*var);
		var = newvar;
	}

	storage->addMinim(*var);
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
