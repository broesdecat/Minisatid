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
#include "external/Translator.hpp"
#include "utils/NumericLimits.hpp"

using namespace MinisatID;

namespace FZ {

class Storage {
private:
	int truelit;
	ExternalConstraintVisitor* store;
	FZTranslator* translator;

	uint nextint;
	std::set<std::string> usednames;
	std::map<std::string, MBoolVar*> name2bool;
	std::map<std::string, MIntVar*> name2int;
	std::map<std::string, MArrayVar<MBoolVar>*> name2boolarray;
	std::map<std::string, MArrayVar<MIntVar>*> name2intarray;
	std::map<std::string, MArrayVar<MSetVar>*> name2setarray;
	std::map<std::string, MSetVar*> name2setvar;

	// TODO garbage collect stuff here

public:
	Storage(ExternalConstraintVisitor* store)
			: truelit(-1), store(store), translator(new FZTranslator()), nextint(1) {
		store->setTranslator(translator);
	}

	void notifyUnsat() {
		store->notifyUnsat();
	}

	MBoolVar* createBoolVar(const std::string& name, bool output) {
		if (usednames.find(name) != usednames.cend()) {
			throw fzexception("Variable already declared");
		}
		usednames.insert(name);
		auto var = new MBoolVar();
		var->var = nextint++;
		name2bool.insert( { name, var });
		extAdd(*store, BoolVar(var->var));
		if (output) {
			translator->setString(var->var, name);
		}
		return var;
	}

	void notifySetVar(const std::string& name, SetVar* var) {
		if (usednames.find(name) != usednames.cend()) {
			throw fzexception("Variable already declared");
		}
		usednames.insert(name);
		auto sv = new MSetVar();
		sv->isrange = var->isrange;
		if(sv->isrange){
			sv->start = var->start;
			sv->end = var->end;
		}else{
			sv->values = var->getValues();
		}
		name2setvar.insert( { name, sv });
	}

	uint createOneShotVar() {
		return nextint++;
	}

	int createOneShotLit() {
		MAssert(nextint<(uint)getMaxElem<int>());
		return nextint++;
	}

	MIntVar* createIntVar(const std::string& name, bool output) {
		if (usednames.find(name) != usednames.cend()) {
			throw fzexception("Variable already declared");
		}
		usednames.insert(name);
		auto var = new MIntVar();
		var->var = nextint++;
		var->hasmap = false;
		var->hasvalue = false;
		name2int.insert( { name, var });
		if (output) {
			translator->addTuple(VarID { var->var }, name);
		}
		return var;
	}

	MArrayVar<MBoolVar>* createBoolArrayVar(const std::string& name, const std::string& outputname, int nbelem, bool output) {
		if (usednames.find(name) != usednames.cend()) {
			throw fzexception("Variable already declared");
		}
		usednames.insert(name);
		auto var = new MArrayVar<MBoolVar>();
		name2boolarray.insert( { name, var });
		for (int i = 1; i <= nbelem; i++) {
			auto boolvar = new MBoolVar();
			boolvar->var = createOneShotVar();
			var->vars.push_back(boolvar);
		}
		if (output) {
			std::vector<Atom> elems;
			for (auto v : var->vars) {
				elems.push_back(v->var);
			}
			translator->addArray(elems, outputname);
		}
		return var;
	}

	MArrayVar<MSetVar>* createSetArrayVar(const std::string& name, const std::string&, int nbelem) {
		if (usednames.find(name) != usednames.cend()) {
			throw fzexception("Variable already declared");
		}
		usednames.insert(name);
		auto var = new MArrayVar<MSetVar>();
		name2setarray.insert( { name, var });
		for (int i = 1; i <= nbelem; i++) {
			auto setvar = new MSetVar();
			var->vars.push_back(setvar);
		}
		return var;
	}

	MArrayVar<MIntVar>* createIntArrayVar(const std::string& name, const std::string& outputname, int nbelem, Var const* const rangevar, bool& nobounds,
			bool output) {
		if (usednames.find(name) != usednames.cend()) {
			throw fzexception("Variable already declared");
		}
		usednames.insert(name);
		auto var = new MArrayVar<MIntVar>();
		name2intarray.insert( { name, var });

		auto intvar = new MIntVar();
		intvar->var = createOneShotVar();
		intvar->hasmap = false;
		intvar->hasvalue = false;
		nobounds = true;
		if (rangevar != NULL) {
			auto rangedvar = dynamic_cast<IntVar const* const >(rangevar);
			if(rangedvar==NULL){
				auto rsvar = dynamic_cast<SetVar const* const >(rangevar);
				if(rsvar!=NULL){
					rangedvar = rsvar->var;
				}else{
					throw idpexception("Unsupported variable type.");
				}
			}
			if (rangedvar->enumvalues) {
				nobounds = false;
				intvar->range = false;
				intvar->values = *rangedvar->values;
			} else if (rangedvar->range) {
				nobounds = false;
				intvar->set(true, rangedvar->begin, rangedvar->end);
			}else{
				nobounds = false;
				intvar->set(true, getMinElem<int>(), getMaxElem<int>());
			}
		}
		for (int i = 1; i <= nbelem; i++) {
			auto tempvar = new MIntVar(*intvar);
			intvar->var = createOneShotVar();
			var->vars.push_back(tempvar);
		}

		if (output) {
			std::vector<VarID> elems;
			for (auto v : var->vars) {
				VarID id;
				id.id = v->var;
				elems.push_back(id);
			}
			translator->addArray(elems, outputname);
		}
		return var;
	}

	MBoolVar* getBoolVar(const std::string& name) {
		auto it = name2bool.find(name);
		if (it == name2bool.end()) {
			std::stringstream ss;
			ss << "Variable " << name << " was not declared.\n";
			throw fzexception(ss.str());
		}
		return (*it).second;
	}

	MIntVar* getIntVar(const std::string& name) {
		auto it = name2int.find(name);
		if (it == name2int.end()) {
			std::stringstream ss;
			ss << "Variable " << name << " was not declared.\n";
			throw fzexception(ss.str());
		}
		return (*it).second;
	}

	MSetVar* getSetVar(const std::string& name) {
		auto it = name2setvar.find(name);
		if (it == name2setvar.end()) {
			std::stringstream ss;
			ss << "Set " << name << " was not declared or not initialized.\n";
			throw fzexception(ss.str());
		}
		return (*it).second;
	}

	MSetVar* getSetVar(const std::string& name, int index) {
		auto it = name2setarray.find(name);
		if (it == name2setarray.end() || (*it).second->vars.size() < (uint) index) {
			throw fzexception("Array was not declared or not initialized.\n");
		}
		return (*it).second->vars[index - 1];
	}

	//IMPORTANT: index starts at ONE, so map to 0 based!
	MBoolVar* getBoolVar(const std::string& name, int index) {
		auto it = name2boolarray.find(name);
		if (it == name2boolarray.end() || (*it).second->vars.size() < (uint) index) {
			throw fzexception("Array was not declared or not initialized.\n");
		}
		return (*it).second->vars[index - 1];
	}

	std::vector<int> getBoolArrayVars(const std::string& name) {
		auto it = name2boolarray.find(name);
		if (it != name2boolarray.end()) {
			std::vector<int> elems;
			for (auto elem : it->second->vars) {
				elems.push_back(elem->var);
			}
			return elems;
		} else {
			std::stringstream ss;
			ss << "Array " << name << " was not declared.\n";
			throw fzexception(ss.str());
		}
	}

	std::vector<bool> getParBoolArrayValues(const std::string& name) {
		auto it = name2boolarray.find(name);
		if (it == name2boolarray.end()) {
			std::stringstream ss;
			ss << "Array " << name << " was not declared.\n";
			throw fzexception(ss.str());
		}
		std::vector<bool> elems;
		for (auto elem : it->second->vars) {
			if (not elem->hasValue()) {
				throw fzexception("Expecting PAR int");
			}
			elems.push_back(elem->getValue());
		}
		return elems;
	}

	std::vector<uint> getIntArrayVars(const std::string& name) {
		auto it = name2intarray.find(name);
		if (it == name2intarray.end()) {
			std::stringstream ss;
			ss << "Array " << name << " was not declared.\n";
			throw fzexception(ss.str());
		}
		std::vector<uint> elems;
		for (auto elem : it->second->vars) {
			elems.push_back(elem->var);
		}
		return elems;
	}

	std::vector<int> getParIntArrayValues(const std::string& name) {
		auto it = name2intarray.find(name);
		if (it == name2intarray.end()) {
			std::stringstream ss;
			ss << "Array " << name << " was not declared.\n";
			throw fzexception(ss.str());
		}
		std::vector<int> elems;
		for (auto elem : it->second->vars) {
			if (not elem->hasValue()) {
				throw fzexception("Expecting PAR int");
			}
			elems.push_back(elem->getValue());
		}
		return elems;
	}

	MIntVar* getIntVar(const std::string& name, int index) {
		auto it = name2intarray.find(name);
		if (it == name2intarray.end() || (*it).second->vars.size() < (uint) index) {
			throw fzexception("Array was not declared or not initialized.\n");
		}
		return (*it).second->vars[index - 1];
	}

	bool isCertainlyUnsat() const {
		return store->isCertainlyUnsat();
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

	uint addCPVar(int begin, int end) {
		MIntVar* var = new MIntVar();
		var->var = createOneShotVar();
		var->set(true, begin, end);
		writeIntVar(*var);
		return var->var;
	}

	MinisatID::Lit get(int lit) {
		return lit > 0 ? mkPosLit(abs(lit)) : mkNegLit(abs(lit));
	}

	std::vector<MinisatID::Lit> get(const std::vector<int>& lits) {
		std::vector<MinisatID::Lit> literals;
		for (auto lit : lits) {
			literals.push_back(get(lit));
		}
		return literals;
	}

	void addBoolExpr(MBoolVar& var, const Expression& expr) {
		if (expr.type == EXPR_BOOL) {
			var.hasvalue = true;
			var.value = expr.boollit;
			extAdd(*store, Disjunction({ expr.boollit ? get(var.var) : ~get(var.var) }));
		} else if (expr.type == EXPR_ARRAYACCESS) {
			var.hasmap = true;
			var.mappedvar = getBoolVar(*expr.arrayaccesslit->id, expr.arrayaccesslit->index);
			extAdd(*store, Implication(get(var.var), ImplicationType::EQUIVALENT, { get(var.mappedvar->var) }, true));
		} else if (expr.type == EXPR_IDENT) {
			var.hasmap = true;
			var.mappedvar = getBoolVar(*expr.ident->name);
			extAdd(*store, Implication(get(var.var), ImplicationType::EQUIVALENT, { get(var.mappedvar->var) }, true));
		} else {
			throw fzexception("Unexpected type in adding bool expression.\n");
		}
	}

	void addSetExpr(MSetVar& var, const Expression& expr) {
		if (expr.type == EXPR_SET) {
			if (isRangeSet(expr)) {
				auto beginend = parseParRangeSet(expr);
				var.start = beginend.first;
				var.end = beginend.second;
				var.isrange = true;
			} else {
				var.values = parseParValueSet(*this, expr);
				var.isrange = false;
			}
		} else {
			throw fzexception("Unsupported type of set expressions.\n");
		}
	}

	std::map<int, const MIntVar&> varid2var;
	const MIntVar& getCPVar(uint id) const {
		return varid2var.at(id);
	}

	void writeIntVar(const MIntVar& var) {
		varid2var.insert( { var.var, var });
		if (var.range) {
			extAdd(*store, IntVarRange(VarID { var.var }, var.begin, var.end));
		} else {
			std::vector<Weight> weights; // TODO var.values should be Weight
			for(auto w: var.values){
				weights.push_back(Weight(w));
			}
			extAdd(*store, IntVarEnum(VarID { var.var }, weights));
		}
	}

	template<class T>
	void addBinI(const T& boolvar, uint intvar, MinisatID::EqType eq, int domelem) {
		extAdd(*store, CPBinaryRel(get(boolvar), VarID { intvar }, eq, domelem));
	}

	template<class T>
	void addBinT(const T& boolvar, uint intvar, MinisatID::EqType eq, uint intvar2) {
		extAdd(*store, CPBinaryRelVar(get(boolvar), VarID { intvar }, eq, { intvar2 }));
	}

	//nobounds implies that it has not been written to output
	void addIntExpr(MIntVar& var, bool nobounds, const Expression& expr) {
		MAssert(not var.hasvalue);
		MAssert(not var.hasmap);
		if (expr.type == EXPR_INT) {
			var.hasvalue = true;
			var.value = expr.intlit;
			if (nobounds) {
				var.set(true, var.value, var.value);
			}
		} else if (expr.type == EXPR_ARRAYACCESS) {
			MAssert(not var.hasvalue);
			assert(nobounds);
			var.hasmap = true;
			auto map = getIntVar(*expr.arrayaccesslit->id, expr.arrayaccesslit->index);
			var.mappedvar = map;
			if (nobounds) {
				var.set(map->range, map->begin, map->end);
				var.values = map->values;
			}
		} else if (expr.type == EXPR_IDENT) {
			var.hasmap = true;
			auto map = getIntVar(*expr.ident->name);
			var.mappedvar = map;
			if (nobounds) {
				var.set(map->range, map->begin, map->end);
				var.values = map->values;
			}
			MAssert(not var.hasvalue);
		} else if(expr.type == EXPR_SET){
			throw fzexception("Unexpected set in int expression.\n");
		} else {
			throw fzexception("Unexpected type in adding int expression.\n");
		}
		MAssert(var.hasvalue || var.hasmap);
	}

	void writeRule(int head, const std::vector<int>& rhs, bool conj, int definitionID) {
		extAdd(*store, MinisatID::Rule(head, get(rhs), conj, definitionID, false));
	}
	void writeEquiv(int head, const std::vector<int>& rhs, bool conj) {
		extAdd(*store, Implication(get(head), ImplicationType::EQUIVALENT, get(rhs), conj));
	}

	template<class T>
	T getRevArg(const std::vector<T>& list, int index) {
		return list[list.size() - index - 1];
	}

	std::vector<Weight> getWeights(const std::vector<int>& ints) {
		std::vector<Weight> weights;
		for (auto w : ints) {
			weights.push_back(w);
		}
		return weights;
	}

	std::vector<VarID> getVarIDs(const std::vector<uint>& ints) {
		std::vector<VarID> uints;
		for (auto w : ints) {
			MAssert(w>0);
			uints.push_back(VarID { w });
		}
		return uints;
	}

	void addLinear(int head, const std::vector<uint> variables, const std::vector<int>& weights, MinisatID::EqType eq, int bound) {
		CPSumWeighted sum(get(head), std::vector<Lit>(variables.size(), get(getTrue())), getVarIDs(variables), getWeights(weights), eq, Weight(bound));
		extAdd(*store, sum);
	}

	void addProduct(int head, const std::vector<uint> variables, int weight, MinisatID::EqType eq, uint varbound) {
		CPProdWeighted sum(get(head), std::vector<Lit>(variables.size(), get(getTrue())), getVarIDs(variables), Weight(weight), eq,
				VarID { varbound });
		extAdd(*store, sum);
	}

	void addLinear(const std::vector<Expression*>& arguments, MinisatID::EqType eq, bool reif) {
		if (arguments.size() != (reif ? 4 : 3)) {
			throw fzexception("Incorrect number of arguments.\n");
		}
		auto weights = parseParIntArray(*this, *getRevArg(arguments, 0));
		auto variables = parseIntArray(*this, *getRevArg(arguments, 1));
		auto bound = parseParInt(*this, *getRevArg(arguments, 2));
		auto head = getTrue();
		if (reif) {
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

	void addOptim(const MIntVar& var, bool minimize) {
		extAdd(*store, OptimizeVar(1, VarID { var.var }, minimize));
	}
};

}
