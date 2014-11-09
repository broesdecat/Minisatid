#pragma once

#include "utils/Utils.hpp"
#include "satsolver/minisat/mtl/Heap.h"
#include "satsolver/minisat/mtl/Vec.h"

namespace Minisat{
class Solver;
}

namespace MinisatID {

struct VarOrderLt {
	const Minisat::vec<double>& acti;
	bool operator ()(Atom x, Atom y) const {
		return acti[x] > acti[y];
	}
	VarOrderLt(const Minisat::vec<double>& act)
			: acti(act) {
	}
};

// General question: is a heuristic responsible for deciding which literals can be decided upon?

class MinisatHeuristic {

public:
	int phase_saving; // Controls the level of phase saving (0=none, 1=limited, 2=full).
	bool rnd_init_act; // Initialize variable activities with a small random value.
	double random_var_freq;
	double var_decay;
protected:
	double var_inc; // Amount to bump next variable with.
	Minisat::vec<double> activity; // A heuristic measurement of the activity of a variable.
	bool rnd_pol; // Use random polarities for branching heuristics.
	Minisat::vec<char> polarity; // The preferred polarity of each variable. True means the variable will have a sign (aka the variable will be assigned false!).
	Minisat::vec<lbool> user_pol; // The users preferred polarity of each variable.
	Minisat::Heap<VarOrderLt> order_heap; // A priority queue of variables ordered with respect to the variable activity.
	Minisat::Solver* S;
private:
	std::vector<int> occurrences;

public:
	MinisatHeuristic(bool rand_pol);
	virtual ~MinisatHeuristic(){}

	virtual void addAtom(Atom v, lbool upol);

	virtual Atom getNextVariable();
	virtual Lit choosePolarity(Atom v);

private:
	void IncreasePriority(Atom v);
	void DecreasePriority(Atom v);
	void adjustPriority(Atom v, double inc); // TODO: make this method protected

public:
	virtual void notifyRestart();
	virtual void notifyNewClause(Minisat::Clause& clause);
	virtual void notifyRemoveClause(Minisat::Clause& clause);
	virtual void notifyConflict(std::vector<Lit>& conflictClause);
	virtual void notifySimplification();
	virtual void notifyBacktrack(Lit l, bool cBiggerThanTrailLimLast);
	virtual void notifyOfLazyAtom(Atom vnew, Atom v1, Atom v2);

	virtual void setPolarity(Atom var, bool makeTrue);
	virtual void initialSetDecidable(Atom v);

	virtual void notifyRandomizedRestart(std::vector<Atom>& affectedVars);
	virtual void notifyAggregate(Atom v);
	virtual void notifyAggPropInit(Atom v);
	virtual void notifyTypedSet(Atom v);
	virtual void notifyHead(Atom v);

	void setSolver(Minisat::Solver* s){S=s;}
	void decayActivity(){var_inc *= (1 / var_decay);}
};

class VarMTF : public MinisatHeuristic {

private:
	double currentMax;
	int nrPushedLits;
	std::vector<int> occurrences;
	std::vector<double> berkAct; // Berkmin activity

	void pushToFront(Atom v);

public:
	VarMTF(int nrPushedLiterals);
	virtual ~VarMTF(){}

	virtual void addAtom(Atom v, lbool upol);

	virtual Atom getNextVariable();
	virtual Lit choosePolarity(Atom v);

public:	
	virtual void notifyRestart();
	virtual void notifyNewClause(Minisat::Clause& clause);
	virtual void notifyRemoveClause(Minisat::Clause& clause);
	virtual void notifyConflict(std::vector<Lit>& conflictClause);
	virtual void notifyOfLazyAtom(Atom vnew, Atom v1, Atom v2);

	virtual void notifyRandomizedRestart(std::vector<Atom>& affectedVars);
	virtual void notifyAggregate(Atom v);
	virtual void notifyAggPropInit(Atom v);
	virtual void notifyTypedSet(Atom v);
	virtual void notifyHead(Atom v);
};

}
