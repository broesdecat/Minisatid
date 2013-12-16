#pragma once

#include <vector>
#include "modules/DPLLTmodule.hpp"
#include "utils/NumericLimits.hpp"

namespace MinisatID{

enum BinComp { BIN_EQ, BIN_LEQ};

class IntVar;

struct IntVarValue{
	IntVar* intvar;
	Lit lit;
	Weight value;

	IntVarValue(IntVar* intvar, Lit lit, Weight value): intvar(intvar), lit(lit), value(value){}
};

class IntVar: public Propagator{
private:
	VarID varid_;
	PCSolver& engine_;
	Weight minvalue, maxvalue;

protected:
	Weight currentmin, currentmax;

	virtual void updateBounds() = 0;

	void setOrigMin(Weight min) {
		minvalue = min;
		currentmin = min;
	}
	void setOrigMax(Weight max) {
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

	Weight origMinValue() const {
		return minvalue;
	}

	Weight origMaxValue() const {
		return maxvalue;
	}

	Weight minValue() const {
		return currentmin;
	}

	Weight maxValue() const {
		return currentmax;
	}

	virtual Lit getLEQLit(Weight bound) = 0;
	virtual Lit getGEQLit(Weight bound) = 0;

private:
	std::map<Weight, Lit> eqlits;
public:

	Lit getEQLit(Weight bound);
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
	RangeIntVar(uint id, PCSolver* solver, VarID varid, Weight min, Weight max);

	virtual void finish();

	virtual int getNbOfFormulas() const { return 1; }

	virtual Lit getLEQLit(Weight bound);
	virtual Lit getGEQLit(Weight bound);
};

class EnumIntVar: public BasicIntVar{
private:
	std::vector<Weight> _values; // SORTED low to high!

public:
	// NOTE: call finish after creation (but allows to first save the intvar without causing propagation
	EnumIntVar(uint id, PCSolver* solver, VarID varid, const std::vector<Weight>& values);

	virtual void finish();

	virtual int getNbOfFormulas() const { return 1; }

	virtual Lit getLEQLit(Weight bound);
	virtual Lit getGEQLit(Weight bound);
};

class LazyIntVar: public IntVar{
private:
	bool halve; // Heuristic optimization to choose to halve the domain or not

	std::vector<IntVarValue> leqlits, savedleqlits; // ORDERED list such that atom <=> intvar =< value

	Lit addVariable(Weight value);
	bool checkAndAddVariable(Weight value, bool defaulttruepol = false);

public:
	LazyIntVar(uint id, PCSolver* solver, VarID varid, Weight min, Weight max);

	virtual void finish();

	virtual void updateBounds();

	virtual void saveState();
	virtual void resetState();
	virtual int getNbOfFormulas() const { return 1; }

	virtual Lit getLEQLit(Weight bound);
	virtual Lit getGEQLit(Weight bound);
};

class IntView{
private:
	IntVar* var_;
	Weight constdiff_;

	Weight constdiff() const { return constdiff_; }

public:
	IntView(IntVar* var, Weight constdiff): var_(var), constdiff_(constdiff){ }

	IntVar* var() const { return var_; }

	VarID getVarID() const { return var()->getVarID(); }

	Weight origMinValue() const {
#ifdef NOARBITPREC
		MAssert(getMaxElem<int>()-constdiff()>var()->origMinValue());
#endif
		return var()->origMinValue()+constdiff();
	}

	Weight origMaxValue() const {
#ifdef NOARBITPREC
		MAssert(getMaxElem<int>()-constdiff()>var()->origMaxValue());
#endif
		return var()->origMaxValue()+constdiff();
	}

	Weight minValue() const {
		auto minval = var()->minValue();
		if(constdiff()>0 && minval+constdiff()<minval){
			return negInfinity();
		}
		if(constdiff()<0 && minval-constdiff()<minval){
			return posInfinity();
		}
		return minval+constdiff();
	}

	Weight maxValue() const {
		auto maxval = var()->maxValue();
		if(constdiff()>0 && maxval+constdiff()<maxval){
			return posInfinity();
		}
		if(constdiff()<0 && maxval-constdiff()<maxval){
			return negInfinity();
		}
		return maxval+constdiff();
	}

	Lit getLEQLit(Weight bound) const {
		if(constdiff()>0 && bound-constdiff()>bound){
			return var()->getPCSolver().getFalseLit();
		}
		if(constdiff()<0 && bound-constdiff()<bound){
			return var()->getPCSolver().getTrueLit();
		}
		return var()->getLEQLit(bound-constdiff());
	}

	Lit getGEQLit(Weight bound) const {
		if(constdiff()>0 && bound-constdiff()>bound){
			return var()->getPCSolver().getTrueLit();
		}
		if(constdiff()<0 && bound-constdiff()<bound){
			return var()->getPCSolver().getFalseLit();
		}
		return var()->getGEQLit(bound-constdiff());
	}

	Lit getEQLit(Weight bound) const{
		return var()->getEQLit(bound);
	}

	Lit getCompareLit(Weight bound, EqType comparison) const {
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
		ss <<var()->toString(getVarID());
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
