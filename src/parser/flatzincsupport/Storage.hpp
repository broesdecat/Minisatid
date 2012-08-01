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

namespace FZ {

class Storage {
private:
	int truelit;
	std::stringstream vars, theory;
	MinisatID::ExternalConstraintVisitor* constraintstorage;
public:
	Storage(MinisatID::ExternalConstraintVisitor* store)
			: truelit(-1), constraintstorage(store) {
	}

	bool isCertainlyUnsat() const {
		return constraintstorage->isCertainlyUnsat();
	}

	void print(std::ostream& stream) {
		stream << vars.str();
		stream << theory.str();
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

	void addBoolExpr(MBoolVar& var, const Expression& expr) {
		if (expr.type == EXPR_BOOL) {
			var.hasvalue = true;
			var.mappedvalue = expr.boollit;
			theory << (expr.boollit ? "" : "-") << var.var << " 0\n";
		} else if (expr.type == EXPR_ARRAYACCESS) {
			var.hasmap = true;
			var.mappedvar = getBoolVar(*expr.arrayaccesslit->id, expr.arrayaccesslit->index)->var;
			theory << "Equiv C " << var.var << " | " << var.mappedvar << " 0\n";
		} else if (expr.type == EXPR_IDENT) {
			var.hasmap = true;
			var.mappedvar = getBoolVar(*expr.ident->name)->var;
			theory << "Equiv C " << var.var << " | " << var.mappedvar << " 0\n";
		} else {
			throw fzexception("Unexpected type.\n");
		}
	}

	void writeIntVar(const MIntVar& var) {
		if (var.range) {
			vars << "INTVAR " << var.var << " " << var.begin << " " << var.end << " 0\n";
		} else {
			vars << "INTVARDOM " << var.var << " ";
			for (auto i = var.values.begin(); i < var.values.end(); ++i) {
				vars << *i << " ";
			}
			vars << " 0\n";
		}
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
		if(var.hasvalue){
			addBinI(getTrue(), var.var, "=", var.mappedvalue);
		}else{
			addBinT(getTrue(), var.var, "=", var.mappedvar);
		}
	}

	void writeRule(int head, const std::vector<int>& rhs, bool conj, int definitionID) {
		theory << (conj ? "C" : "D") <<" " << definitionID << " | " << head << " <- ";
		for (auto i = rhs.begin(); i < rhs.end(); ++i) {
			theory << *i << " ";
		}
		theory << " 0\n";
	}
	void writeEquiv(int head, const std::vector<int>& rhs, bool conj) {
		theory << "Equiv " << (conj ? "C" : "D") << " " << head << " ";
		for (auto i = rhs.begin(); i < rhs.end(); ++i) {
			theory << *i << " ";
		}
		theory << " 0\n";
	}

	template<class T>
	void addBinI(const T& boolvar, int intvar, const std::string& op, int intvar2) {
		theory << "BINTRI" << " " << boolvar << " " << intvar << " " << op << " " << intvar2 << " 0\n";
	}

	template<class T>
	void addBinT(const T& boolvar, int intvar, const std::string& op, int intvar2) {
		theory << "BINTRT" << " " << boolvar << " " << intvar << " " << op << " " << intvar2 << " 0\n";
	}

	template<class T>
	T getRevArg(const std::vector<T>& list, int index) {
		return list[list.size() - index - 1];
	}

	void addLinear(const std::vector<Expression*>& arguments, const std::string& op, bool reif) {
		if (arguments.size() != (reif ? 4 : 3)) {
			throw fzexception("Incorrect number of arguments.\n");
		}
		auto weights = parseParIntArray(*this, *getRevArg(arguments, 0));
		auto variables = parseArray(*this, VAR_INT, *getRevArg(arguments, 1));
		int intvar = parseParInt(*this, *getRevArg(arguments, 2));
		theory << "CPSUM ";
		if (reif) {
			theory << parseBool(*this, *getRevArg(arguments, 3)) << " ";
		} else {
			theory << getTrue() << " ";
		}
		for (unsigned int i = 0; i < variables.size(); ++i) {
			theory << variables[i] << " ";
		}
		theory << " | ";
		for (unsigned int i = 0; i < weights.size(); ++i) {
			theory << weights[i] << " ";
		}
		theory << " " << op << " " << intvar << " 0\n";
	}

	void addClause(const std::vector<int>& poslits, const std::vector<int>& neglits) {
		for (auto i = poslits.begin(); i < poslits.end(); ++i) {
			theory << *i << " ";
		}
		for (auto i = neglits.begin(); i < neglits.end(); ++i) {
			theory << "-" << *i << " ";
		}
		theory << " 0\n";
	}

	void addMinim(MIntVar* var) {
		// FIXME
	}
};

}
