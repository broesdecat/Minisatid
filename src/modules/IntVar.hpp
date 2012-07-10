#ifndef INTVAR_HPP
#define INTVAR_HPP

#include <vector>
#include "modules/DPLLTmodule.hpp"

namespace MinisatID{

enum BinComp { BIN_EQ, BIN_LEQ};

class IntVar;

struct IntVarValue{
	IntVar* intvar;
	Var atom;
	int value;

	IntVarValue(IntVar* intvar, Var atom, int value): intvar(intvar), atom(atom), value(value){}
};

class IntVar: public Propagator{
private:
	static int maxid_;
	int id_, origid_;
	PCSolver& engine_;
	int minvalue, maxvalue;

protected:
	int currentmin, currentmax;

	virtual void updateBounds() = 0;

	void setOrigMin(int min) {
		minvalue = min;
		currentmin = min;
	}
	void setOrigMax(int max) {
		maxvalue = max;
		currentmax = max;
	}

	void addConstraint(IntVarValue const * const prev, const IntVarValue& lv, IntVarValue const * const next);

public:
	IntVar(PCSolver* solver, int origid);

	virtual void accept(ConstraintVisitor& visitor);
	virtual rClause	notifypropagate();
	virtual void notifyBacktrack(int untillevel, const Lit& decision);
	virtual rClause getExplanation(const Lit&){ throw idpexception("Error: incorrect execution path.");}
	virtual void notifyNewDecisionLevel(){ throw idpexception("Error: incorrect execution path."); }
	virtual void notifyBacktrackDecisionLevel(int, const Lit&){ throw idpexception("Error: incorrect execution path."); }

	int id() const { return id_; }
	int origid() const { return origid_; }
	PCSolver& engine() { return engine_; }

	int origMinValue() const {
		return minvalue;
	}

	int origMaxValue() const {
		return maxvalue;
	}

	int minValue() const {
		return currentmin;
	}

	int maxValue() const {
		return currentmax;
	}

	virtual Lit getLEQLit(int bound) = 0;
	virtual Lit getGEQLit(int bound) = 0;
};

class BasicIntVar: public IntVar{
protected:
	std::vector<IntVarValue> leqlits; // eq[i] =< minvalue+i

	void addConstraints();

public:
	BasicIntVar(PCSolver* solver, int origid);

	virtual void updateBounds();
};

class RangeIntVar: public BasicIntVar{
public:
	RangeIntVar(PCSolver* solver, int origid, int min, int max);

	virtual int getNbOfFormulas() const { return 1; }

	virtual Lit getLEQLit(int bound);
	virtual Lit getGEQLit(int bound);
};

class EnumIntVar: public BasicIntVar{
private:
	std::vector<int> _values; // SORTED low to high!

public:
	EnumIntVar(PCSolver* solver, int origid, const std::vector<int>& values);

	virtual int getNbOfFormulas() const { return 1; }

	virtual Lit getLEQLit(int bound);
	virtual Lit getGEQLit(int bound);
};

class LazyIntVar: public IntVar{
private:
	std::vector<IntVarValue> leqlits; // ORDERED list such that atom <=> intvar =< value

	Lit checkAddVariable(int value);

public:
	LazyIntVar(PCSolver* solver, int origid, int min, int max);

	virtual void updateBounds();

	virtual int getNbOfFormulas() const { return 1; }

	virtual Lit getLEQLit(int bound);
	virtual Lit getGEQLit(int bound);
};

class IntView{
private:
	IntVar* var_;
	int constdiff_;

	int constdiff() const { return constdiff_; }

public:
	IntView(IntVar* var, int constdiff): var_(var), constdiff_(constdiff){ }

	IntVar* var() const { return var_; }

	int id() const { return var()->id(); }
	int origid() const { return var()->origid(); }

	int origMinValue() const {
		return var()->origMinValue()+constdiff();
	}

	int origMaxValue() const {
		return var()->origMaxValue()+constdiff();
	}

	int minValue() const {
		return var()->minValue()+constdiff();
	}

	int maxValue() const {
		return var()->maxValue()+constdiff();
	}

	Lit getLEQLit(int bound) const {
		return var()->getLEQLit(bound-constdiff());
	}

	Lit getGEQLit(int bound) const {
		return var()->getGEQLit(bound-constdiff());
	}

	std::string toString() const {
		std::stringstream ss;
		ss <<"var" <<origid();
		if(constdiff_!=0){
			if(constdiff_>0){
				ss <<"+";
			}
			ss <<constdiff_;
		}
		return ss.str();
	}
};

}

#endif //INTVAR_HPP
