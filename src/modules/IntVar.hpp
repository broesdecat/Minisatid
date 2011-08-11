#ifndef INTVAR_HPP
#define INTVAR_HPP

#include <vector>
#include "utils/Utils.hpp"
#include "modules/DPLLTmodule.hpp"
#include "theorysolvers/PCSolver.hpp"

namespace MinisatID{

enum BinComp { BIN_EQ, BIN_LEQ};

class IntVar;

struct IntVarValue{
	IntVar* var;
	bool 	eq;
	Weight value;

	IntVarValue(IntVar* var, bool eq, Weight value): var(var), eq(eq), value(value){}
};

class IntVar: public Propagator{
private:
	static int maxid_;
	static std::map<int, IntVarValue> var2intvarvalues;
	int id_, origid_;
	PCSolver& engine_;
	const int minvalue, maxvalue;
	int offset, currentmin, currentmax;
	std::vector<Var> equalities;	// eq[i] == minvalue+i
	std::vector<Var> disequalities; // eq[i] =< minvalue+i
	// given atom, its meaning is eq[atom-offset]
	
public:
	IntVar(PCSolver* solver, int origid, int min, int max);

	static const IntVarValue& getIntVar(const Lit& lit) { return var2intvarvalues.at(var(lit)); }

	virtual const char* getName() const { return "intvar"; }
	virtual void finishParsing(bool& present, bool& unsat);
	virtual void notifyBacktrack(int untillevel, const Lit& decision);
	virtual rClause	notifypropagate();

	int id() const { return id_; }
	int origid() const { return origid_; }
	PCSolver& engine() { return engine_; }

	int origMinValue(){
		return minvalue;
	}

	int origMaxValue(){
		return maxvalue;
	}

	int minValue(){
		return currentmin;
	}

	int maxValue(){
		return currentmax;
	}

	Lit getLEQLit(int bound){
		return mkPosLit(disequalities[bound-minvalue]);
	}

	Lit getGEQLit(int bound){
		return mkNegLit(disequalities[bound-minvalue-1]);
	}

	Lit getEQLit(int bound){
		return mkPosLit(equalities[bound-minvalue]);
	}

	Lit getNEQLit(int bound){
		return mkNegLit(equalities[bound-minvalue]);
	}

private:
	void addConstraints();
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

	int origMinValue(){
		return var()->origMinValue()+constdiff();
	}

	int origMaxValue(){
		return var()->origMaxValue()+constdiff();
	}

	int minValue(){
		return var()->minValue()+constdiff();
	}

	int maxValue(){
		return var()->maxValue()+constdiff();
	}

	Lit getLEQLit(int bound){
		return var()->getLEQLit(bound-constdiff());
	}

	Lit getGEQLit(int bound){
		return var()->getGEQLit(bound-constdiff());
	}

	Lit getEQLit(int bound){
		return var()->getEQLit(bound-constdiff());
	}

	Lit getNEQLit(int bound){
		return var()->getNEQLit(bound-constdiff());
	}
};

}

#endif //INTVAR_HPP
