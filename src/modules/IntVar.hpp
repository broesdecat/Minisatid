#ifndef INTVAR_HPP
#define INTVAR_HPP

#include <vector>
#include "utils/Utils.hpp"
#include "modules/DPLLTmodule.hpp"
#include "theorysolvers/PCSolver.hpp"

namespace MinisatID{

enum BinComp { BIN_EQ, BIN_NEQ, BIN_L, BIN_LEQ};

class IntVar: public Propagator{
private:
	static int maxid_;
	int id_, origid_;
	PCSolver& engine_;
	int offset, minvalue, maxvalue, currentmin, currentmax;
	std::vector<Var> equalities;	// eq[i] == minvalue+i
	std::vector<Var> disequalities; // eq[i] =< minvalue+i
	// given atom, its meaning is eq[atom-offset]
	
public:
	IntVar(PCSolver* solver, int origid, int min, int max);

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

}

#endif //INTVAR_HPP
