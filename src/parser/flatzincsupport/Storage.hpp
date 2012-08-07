/*
 * Storage.hpp
 *
 *  Created on: Aug 1, 2012
 *      Author: broes
 */

#pragma once

#include <cassert>
#include "fzexception.hpp"
#include "external/ConstraintAdditionInterface.hpp"
#include "external/Constraints.hpp"

using namespace MinisatID;

namespace FZ {

class Storage {
private:
	uint maxid;
	int truelit;
	ExternalConstraintVisitor* store;

	int nextint;
	std::map<std::string, MBoolVar*> name2bool;
	std::map<std::string, MIntVar*> name2int;
	std::map<std::string, MBoolArrayVar*> name2boolarray;
	std::map<std::string, MIntArrayVar*> name2intarray;

public:
	Storage(ExternalConstraintVisitor* store)
			: maxid(1), truelit(-1), store(store), nextint(1) {
	}

	MBoolVar* createBoolVar(const std::string& name) {
		auto var = new MBoolVar();
		var->var = nextint++;
		var->hasmap = false;
		var->hasvalue = false;
		name2bool.insert({name, var});
		return var;
	}

	int createOneShotVar() {
		return nextint++;
	}

	MIntVar* createIntVar(const std::string& name) {
		auto var = new MIntVar();
		var->var = nextint++;
		var->hasmap = false;
		var->hasvalue = false;
		name2int.insert({name, var});
		return var;
	}

	MBoolArrayVar* createBoolArrayVar(const std::string& name, int nbelem) {
		auto var = new MBoolArrayVar();
		var->nbelem = nbelem;
		name2boolarray.insert({name, var});
		return var;
	}

	MIntArrayVar* createIntArrayVar(const std::string& name, int nbelem) {
		auto var = new MIntArrayVar();
		var->nbelem = nbelem;
		name2intarray.insert({name, var});
		return var;
	}

	MBoolVar* getBoolVar(const std::string& name) {
		auto it = name2bool.find(name);
		if (it == name2bool.end()) {
			throw fzexception("Variable was not declared.\n");
		}
		return (*it).second;
	}

	MIntVar* getIntVar(const std::string& name) {
		auto it = name2int.find(name);
		if (it == name2int.end()) {
			throw fzexception("Variable was not declared.\n");
		}
		return (*it).second;
	}

	//IMPORTANT: index starts at ONE, so map to 0 based!
	MBoolVar* getBoolVar(const std::string& name, int index) {
		auto it = name2boolarray.find(name);
		if (it == name2boolarray.end() || (*it).second->vars.size() < (uint)index) {
			throw fzexception("Array was not declared or not initialized.\n");
		}
		return (*it).second->vars[index - 1];
	}

	MIntVar* getIntVar(const std::string& name, int index) {
		auto it = name2intarray.find(name);
		if (it == name2intarray.end() || (*it).second->vars.size() < (uint)index) {
			throw fzexception("Array was not declared or not initialized.\n");
		}
		return (*it).second->vars[index - 1];
	}

	int getVar(const std::string& name, bool expectbool) {
		if (expectbool) {
			return getBoolVar(name)->var;
		} else {
			return getIntVar(name)->var;
		}
	}

	int getVar(const std::string& name, int index, bool expectbool) {
		if (expectbool) {
			return getBoolVar(name, index)->var;
		} else {
			return getIntVar(name, index)->var;
		}
	}




	bool isCertainlyUnsat() const {
		return store->isCertainlyUnsat();
	}

	void print(std::ostream&) {
	}

	int getTrue() {
		if (truelit == -1) {
			truelit = createOneShotVar();
			addClause( { truelit }, { });
		}
		return truelit;
	}

	int getFalse() {
		return -getTrue();
	}

	int addCPVar(int begin, int end) {
		int varnb = createOneShotVar();
		MIntVar var;
		var.set(varnb, begin, end);
		writeIntVar(var);
		return varnb;
	}

	MinisatID::Lit get(int lit){
		return lit>0?mkPosLit(lit):mkNegLit(lit);
	}

	std::vector<MinisatID::Lit> get(const std::vector<int>& lits){
		std::vector<MinisatID::Lit> literals;
		for(auto lit: lits){
			literals.push_back(get(lit));
		}
		return literals;
	}

	void addBoolExpr(MBoolVar& var, const Expression& expr) {
		if (expr.type == EXPR_BOOL) {
			var.hasvalue = true;
			var.mappedvalue = expr.boollit;
			extAdd(*store, Disjunction(maxid++, { expr.boollit ? get(var.var) : get(var.var) }));
		} else if (expr.type == EXPR_ARRAYACCESS) {
			var.hasmap = true;
			var.mappedvar = getBoolVar(*expr.arrayaccesslit->id, expr.arrayaccesslit->index)->var;
			extAdd(*store, Implication(maxid++,get(var.var), ImplicationType::EQUIVALENT, { get(var.mappedvar) }, true));
		} else if (expr.type == EXPR_IDENT) {
			var.hasmap = true;
			var.mappedvar = getBoolVar(*expr.ident->name)->var;
			extAdd(*store, Implication(maxid++,get(var.var), ImplicationType::EQUIVALENT, { get(var.mappedvar) }, true));
		} else {
			throw fzexception("Unexpected type.\n");
		}
	}

	std::map<int, MIntVar> varid2var;
	const MIntVar& getCPVar(int id) const{
		return varid2var.at(id);
	}

	void writeIntVar(const MIntVar& var) {
		if (var.range) {
			extAdd(*store, IntVarRange(maxid++,{var.var}, var.begin, var.end));
		} else {
			extAdd(*store, IntVarEnum(maxid++,{var.var}, var.values));
		}
	}

	template<class T>
	void addBinI(const T& boolvar, int intvar, MinisatID::EqType eq, int domelem) {
		extAdd(*store, CPBinaryRel(maxid++,get(boolvar).getAtom(), {intvar}, eq, domelem));
	}

	template<class T>
	void addBinT(const T& boolvar, int intvar, MinisatID::EqType eq, int intvar2) {
		extAdd(*store, CPBinaryRel(maxid++,get(boolvar).getAtom(), {intvar}, eq, {intvar2}));
	}

	//nobounds implies that it has not been written to output
	void addIntExpr(MIntVar& var, bool nobounds, const Expression& expr) {
		if (expr.type == EXPR_INT) {
			var.hasvalue = true;
			var.mappedvalue = expr.intlit;
			if (nobounds) {
				var.set(true, var.mappedvalue, var.mappedvalue);
			}
		} else if (expr.type == EXPR_ARRAYACCESS) {
			assert(nobounds);
			var.hasmap = true;
			auto map = getIntVar(*expr.arrayaccesslit->id, expr.arrayaccesslit->index);
			var.mappedvar = map->var;
			if (nobounds) {
				var.set(map->range, map->begin, map->end);
				var.values = map->values;
			}
		} else if (expr.type == EXPR_IDENT) {
			var.hasmap = true;
			auto map = getIntVar(*expr.ident->name);
			var.mappedvar = map->var;
			if (nobounds) {
				var.set(map->range, map->begin, map->end);
				var.values = map->values;
			}
		} else {
			throw fzexception("Unexpected type.\n");
		}
		if (var.hasvalue) {
			addBinI(getTrue(), var.var, EqType::EQ, var.mappedvalue);
		} else {
			addBinT(getTrue(), var.var, EqType::EQ, var.mappedvar);
		}
	}

	void writeRule(int head, const std::vector<int>& rhs, bool conj, int definitionID) {
		extAdd(*store, MinisatID::Rule(maxid++,head, get(rhs), conj, definitionID));
	}
	void writeEquiv(int head, const std::vector<int>& rhs, bool conj) {
		extAdd(*store, Implication(maxid++,get(head), ImplicationType::EQUIVALENT, get(rhs), conj));
	}

	template<class T>
	T getRevArg(const std::vector<T>& list, int index) {
		return list[list.size() - index - 1];
	}

	std::vector<Weight> getWeights(const std::vector<int>& ints){
		std::vector<Weight> weights;
		for(auto w:ints){
			weights.push_back(w);
		}
		return weights;
	}

	std::vector<VarID> getVarIDs(const std::vector<int>& ints){
		std::vector<VarID> uints;
		for(auto w:ints){
			MAssert(w>0);
			uints.push_back({w});
		}
		return uints;
	}

	void addLinear(int head, const std::vector<int> variables, const std::vector<int>& weights, MinisatID::EqType eq, int bound){
		CPSumWeighted sum(maxid++,get(head).getAtom(), getVarIDs(variables), getWeights(weights), eq, Weight(bound));
		extAdd(*store, sum);
	}

	void addProduct(int head, const std::vector<int> variables, int weight, MinisatID::EqType eq, int varbound){
		CPProdWeighted sum(maxid++,get(head).getAtom(), getVarIDs(variables), Weight(weight), eq, {varbound});
		extAdd(*store, sum);
	}

	void addLinear(const std::vector<Expression*>& arguments, MinisatID::EqType eq, bool reif) {
		if (arguments.size() != (reif ? 4 : 3)) {
			throw fzexception("Incorrect number of arguments.\n");
		}
		auto weights = parseParIntArray(*this, *getRevArg(arguments, 0));
		auto variables = parseArray(*this, VAR_INT, *getRevArg(arguments, 1));
		auto bound = parseParInt(*this, *getRevArg(arguments, 2));
		auto head = getTrue();
		if(reif){
			head = parseBool(*this, *getRevArg(arguments, 3));
		}
		addLinear(head, variables, weights, eq, bound);
	}

	void addClause(const std::vector<int>& poslits, const std::vector<int>& neglits) {
		Disjunction d(maxid++,get(poslits));
		for (auto i : neglits) {
			d.literals.push_back(get(-i));
		}
		extAdd(*store, d);
	}

	void addMinim(const MIntVar& var) {
		writeIntVar(var);
		extAdd(*store, MinimizeVar(1, {var.var}));
	}
};

}
