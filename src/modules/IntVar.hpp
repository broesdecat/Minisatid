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
	Weight value;

	IntVarValue(IntVar* intvar, Var atom, Weight value): intvar(intvar), atom(atom), value(value){}
};

// FIXME how are these values returned to the grounder???
class IntVar: public Propagator{
private:
	static int maxid_;
	int id_, origid_;
	PCSolver& engine_;
	const int minvalue, maxvalue;
	int offset, currentmin, currentmax;
	std::vector<IntVarValue> leqlits; // eq[i] =< minvalue+i
	// given atom, its meaning is eq[atom-offset]
	
	void updateBounds();

public:
	IntVar(PCSolver* solver, int origid, int min, int max);

	virtual void accept(ConstraintVisitor& visitor);
	virtual rClause	notifypropagate();
	virtual void notifyBacktrack(int untillevel, const Lit& decision);
	virtual int getNbOfFormulas() const { return maxvalue-minvalue*2; }
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

	Lit getLEQLit(int bound) const;
	Lit getGEQLit(int bound) const;

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
