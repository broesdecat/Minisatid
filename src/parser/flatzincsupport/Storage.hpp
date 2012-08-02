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
	int truelit;
	ExternalConstraintVisitor* store;
public:
	Storage(ExternalConstraintVisitor* store)
			: truelit(-1), store(store) {
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

	MinisatID::Literal get(int lit){
		return lit>0?mkPosLit(lit):mkNegLit(lit);
	}

	std::vector<MinisatID::Literal> get(const std::vector<int>& lits){
		std::vector<MinisatID::Literal> literals;
		for(auto lit: lits){
			literals.push_back(get(lit));
		}
		return literals;
	}

	void addBoolExpr(MBoolVar& var, const Expression& expr) {
		if (expr.type == EXPR_BOOL) {
			var.hasvalue = true;
			var.mappedvalue = expr.boollit;
			extAdd(*store, Disjunction( { expr.boollit ? get(var.var) : get(var.var) }));
		} else if (expr.type == EXPR_ARRAYACCESS) {
			var.hasmap = true;
			var.mappedvar = getBoolVar(*expr.arrayaccesslit->id, expr.arrayaccesslit->index)->var;
			extAdd(*store, Implication(get(var.var), ImplicationType::EQUIVALENT, { get(var.mappedvar) }, true));
		} else if (expr.type == EXPR_IDENT) {
			var.hasmap = true;
			var.mappedvar = getBoolVar(*expr.ident->name)->var;
			extAdd(*store, Implication(get(var.var), ImplicationType::EQUIVALENT, { get(var.mappedvar) }, true));
		} else {
			throw fzexception("Unexpected type.\n");
		}
	}

	void writeIntVar(const MIntVar& var) {
		if (var.range) {
			extAdd(*store, IntVarRange(var.var, var.begin, var.end));
		} else {
			extAdd(*store, IntVarEnum(var.var, var.values));
		}
	}

	template<class T>
	void addBinI(const T& boolvar, int intvar, MinisatID::EqType eq, int domelem) {
		extAdd(*store, CPBinaryRel(get(boolvar).getAtom(), intvar, eq, domelem));
	}

	template<class T>
	void addBinT(const T& boolvar, int intvar, MinisatID::EqType eq, int intvar2) {
		extAdd(*store, CPBinaryRel(get(boolvar).getAtom(), intvar, eq, intvar2));
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
		extAdd(*store, MinisatID::Rule(head, get(rhs), conj, definitionID));
	}
	void writeEquiv(int head, const std::vector<int>& rhs, bool conj) {
		extAdd(*store, Implication(get(head), ImplicationType::EQUIVALENT, get(rhs), conj));
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

	std::vector<uint> getUints(const std::vector<int>& ints){
		std::vector<uint> uints;
		for(auto w:ints){
			MAssert(w>0);
			uints.push_back((uint)w);
		}
		return uints;
	}

	void addLinear(int head, const std::vector<int> variables, const std::vector<int>& weights, MinisatID::EqType eq, int bound){
		CPSumWeighted sum(get(head).getAtom(), getUints(variables), getWeights(weights), eq, Weight(bound));
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
		Disjunction d(get(poslits));
		for (auto i : neglits) {
			d.literals.push_back(get(-i));
		}
		extAdd(*store, d);
	}

	void addMinim(const MIntVar& var) {
		writeIntVar(var);
		extAdd(*store, MinimizeVar(1, var.var));
	}
};

}
