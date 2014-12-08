#pragma once

#include <vector>
#include "modules/DPLLTmodule.hpp"
#include "utils/NumericLimits.hpp"

namespace MinisatID{

class PropagatorFactory;

enum BinComp { BIN_EQ, BIN_LEQ};

class PCSolver;
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

	Lit noimagelit; // If true, make all leqlits true (arbitrary choice, to prevent spurious models)

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

	IntVar(PCSolver* solver, VarID varid, Lit partial);

public:
	virtual void accept(ConstraintVisitor& visitor);
	virtual rClause	notifypropagate();
	virtual void notifyBacktrack(int untillevel, const Lit& decision);
	virtual rClause getExplanation(const Lit&){ throw idpexception("Error: incorrect execution path.");}
	virtual void notifyNewDecisionLevel(){ throw idpexception("Error: incorrect execution path."); }

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

	bool certainlyHasImage() const;
	bool possiblyHasImage() const;

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
	Lit getNoImageLit() const{
		return noimagelit;
	}
	Lit getEQLit(Weight bound);

	bool possiblyNondenoting() const;
};

void addPartialChecks(Propagator* origin, std::vector<IntView*> views, const Lit& head);

class BasicIntVar: public IntVar{
protected:
	std::vector<IntVarValue> leqlits; // eq[i] =< minvalue+i

	void addConstraints();

	BasicIntVar(PCSolver* solver, VarID varid, Lit partial);

public:
	virtual void updateBounds();
};

class RangeIntVar: public BasicIntVar{
private:
	friend class PropagatorFactory;
	// NOTE: call finish after creation (but allows to first save the intvar without causing propagation
	RangeIntVar(PCSolver* solver, VarID varid, Weight min, Weight max, Lit partial);

public:
	virtual void finish();

	virtual int getNbOfFormulas() const { return 1; }

	virtual Lit getLEQLit(Weight bound);
	virtual Lit getGEQLit(Weight bound);
};

class EnumIntVar: public BasicIntVar{
private:
	std::vector<Weight> _values; // SORTED low to high!

	friend class PropagatorFactory;
	// NOTE: call finish after creation (but allows to first save the intvar without causing propagation
	EnumIntVar(PCSolver* solver, VarID varid, const std::vector<Weight>& values, Lit partial);

public:
	virtual void finish();

	virtual int getNbOfFormulas() const { return 1; }

	virtual Lit getLEQLit(Weight bound);
	virtual Lit getGEQLit(Weight bound);
};

class LazyIntVar: public IntVar{
private:
	bool halve; // Heuristic optimization to choose to halve the domain or not

	std::vector<IntVarValue> leqlits; // ORDERED list such that atom <=> intvar =< value

	Lit addVariable(Weight value);
	bool checkAndAddVariable(Weight value);

	friend class PropagatorFactory;
	LazyIntVar(PCSolver* solver, VarID varid, Weight min, Weight max, Lit partial);

public:
	virtual void finish();

	virtual void updateBounds();
  
	virtual int getNbOfFormulas() const { return 1; }

	virtual Lit getLEQLit(Weight bound);
	virtual Lit getGEQLit(Weight bound);
};

class EventQueue;

class IntView{
private:
	IntVar* var_; // orig var
	Weight constdiff_;

	friend class EventQueue;
	friend class PropagatorFactory;

	VarID id; // additional id
	IntVar* var() const { return var_; }
	VarID getVarID() const { return var()->getVarID(); }

public:
	IntView(IntVar* var, VarID id, Weight constdiff): var_(var), constdiff_(constdiff), id(id) { }

	VarID getID() const { return id; }
	Weight getFixedDiff() const { return constdiff_; }

	Weight origMinValue() const {
#ifdef NOARBITPREC
		MAssert(getMaxElem<int>()-getFixedDiff()>var()->origMinValue());
#endif
		return var()->origMinValue()+getFixedDiff();
	}

	Weight origMaxValue() const {
#ifdef NOARBITPREC
		MAssert(getMaxElem<int>()-getFixedDiff()>var()->origMaxValue());
#endif
		return var()->origMaxValue()+getFixedDiff();
	}

	Weight minValue() const {
		auto minval = var()->minValue();
		if(getFixedDiff()>0 && minval+getFixedDiff()<minval){
			return negInfinity();
		}
		if(getFixedDiff()<0 && minval-getFixedDiff()<minval){
			return posInfinity();
		}
		return minval+getFixedDiff();
	}

	Weight maxValue() const {
		auto maxval = var()->maxValue();
		if(getFixedDiff()>0 && maxval+getFixedDiff()<maxval){
			return posInfinity();
		}
		if(getFixedDiff()<0 && maxval-getFixedDiff()<maxval){
			return negInfinity();
		}
		return maxval+getFixedDiff();
	}

	Lit getLEQLit(Weight bound) const {
		if(getFixedDiff()>0 && bound-getFixedDiff()>bound){
			return var()->getPCSolver().getFalseLit();
		}
		if(getFixedDiff()<0 && bound-getFixedDiff()<bound){
			return var()->getPCSolver().getTrueLit();
		}
		return var()->getLEQLit(bound-getFixedDiff());
	}

	Lit getGEQLit(Weight bound) const {
		if(getFixedDiff()>0 && bound-getFixedDiff()>bound){
			return var()->getPCSolver().getTrueLit();
		}
		if(getFixedDiff()<0 && bound-getFixedDiff()<bound){
			return var()->getPCSolver().getFalseLit();
		}
		return var()->getGEQLit(bound-getFixedDiff());
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
		return not possiblyHasImage() || minValue()==maxValue();
	}

	Lit getNoImageLit() const {
		return var()->getNoImageLit();
	}
	bool certainlyHasImage() const{
		return var()->certainlyHasImage();
	}
	bool possiblyHasImage() const{
		return var()->possiblyHasImage();
	}
	bool isPartial() const{
		return var()->possiblyNondenoting();
	}

	std::string toString() const {
		std::stringstream ss;
		ss <<var()->toString(var()->getVarID());
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
