#ifndef INTVAR_HPP
#define INTVAR_HPP

#include <vector>
#include "modules/DPLLTmodule.hpp"
#include "utils/NumericLimits.hpp"

namespace MinisatID{

enum BinComp { BIN_EQ, BIN_LEQ};

class IntVar;

struct IntVarValue{
	IntVar* intvar;
	Atom atom;
	int value;

	IntVarValue(IntVar* intvar, Atom atom, int value): intvar(intvar), atom(atom), value(value){}
};

class IntVar: public Propagator{
private:
	VarID varid_;
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
	IntVar(uint id, PCSolver* solver, VarID varid);

	virtual void accept(ConstraintVisitor& visitor);
	virtual rClause	notifypropagate();
	virtual void notifyBacktrack(int untillevel, const Lit& decision);
	virtual rClause getExplanation(const Lit&){ throw idpexception("Error: incorrect execution path.");}
	virtual void notifyNewDecisionLevel(){ throw idpexception("Error: incorrect execution path."); }
	virtual void notifyBacktrackDecisionLevel(int, const Lit&){ throw idpexception("Error: incorrect execution path."); }

	// NOTE: required because intvars are both data and propagator, and the data is required earlier then propagation is allowed (when lazy grounding)
	virtual void finish() = 0;

	VarID getVarID() const { return varid_; }
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

private:
	std::map<int, Lit> eqlits;
public:
	Lit getEQLit(int bound);
};

class BasicIntVar: public IntVar{
protected:
	std::vector<IntVarValue> leqlits; // eq[i] =< minvalue+i

	void addConstraints();

public:
	BasicIntVar(uint id, PCSolver* solver, VarID varid);

	virtual void updateBounds();
};

class RangeIntVar: public BasicIntVar{
public:
	// NOTE: call finish after creation (but allows to first save the intvar without causing propagation
	RangeIntVar(uint id, PCSolver* solver, VarID varid, int min, int max);

	virtual void finish();

	virtual int getNbOfFormulas() const { return 1; }

	virtual Lit getLEQLit(int bound);
	virtual Lit getGEQLit(int bound);
};

class EnumIntVar: public BasicIntVar{
private:
	std::vector<int> _values; // SORTED low to high!

public:
	// NOTE: call finish after creation (but allows to first save the intvar without causing propagation
	EnumIntVar(uint id, PCSolver* solver, VarID varid, const std::vector<int>& values);

	virtual void finish();

	virtual int getNbOfFormulas() const { return 1; }

	virtual Lit getLEQLit(int bound);
	virtual Lit getGEQLit(int bound);
};

class LazyIntVar: public IntVar{
private:
	bool halve; // Heuristic optimization to choose to halve the domain or not
	std::vector<IntVarValue> leqlits, savedleqlits; // ORDERED list such that atom <=> intvar =< value

	Lit addVariable(int value);
	bool checkAndAddVariable(int value, bool defaulttruepol = false);

public:
	LazyIntVar(uint id, PCSolver* solver, VarID varid, int min, int max);

	virtual void finish();

	virtual void updateBounds();

	virtual void saveState();
	virtual void resetState();
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

	VarID getVarID() const { return var()->getVarID(); }

	int origMinValue() const {
		MAssert(getMaxElem<int>()-constdiff()>var()->origMinValue());
		return var()->origMinValue()+constdiff();
	}

	int origMaxValue() const {
		MAssert(getMaxElem<int>()-constdiff()>var()->origMaxValue());
		return var()->origMaxValue()+constdiff();
	}

	int minValue() const;

	int maxValue() const;

	Lit getLEQLit(int bound) const;

	Lit getGEQLit(int bound) const;

	Lit getEQLit(int bound) const{
		return var()->getEQLit(bound);
	}

	Lit getCompareLit(int bound, EqType comparison) const {
		switch (comparison) {
		case EqType::LEQ:
			return getLEQLit(bound);
		case EqType::L:
			return !getGEQLit(bound);
		case EqType::GEQ:
			return getGEQLit(bound);
		case EqType::G:
			return !getLEQLit(bound);
		case EqType::EQ:
			return getEQLit(bound);
		case EqType::NEQ:
			return !getEQLit(bound);
		}
		MAssert(false);
		return getLEQLit(bound);
	}

	bool isKnown() const{
		return minValue()==maxValue();
	}

	std::string toString() const {
		std::stringstream ss;
		ss <<"var" <<var()->toString(getVarID());
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
