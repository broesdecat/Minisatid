/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef AGGSET_HPP_
#define AGGSET_HPP_

#include <vector>
#include <algorithm>
#include <cmath>

#include "modules/DPLLTmodule.hpp"
#include "modules/aggsolver/AggUtils.hpp"
#include "modules/aggsolver/AggTransform.hpp"

namespace MinisatID {

class TypedSet: public Propagator {
protected:
	vwl wl; // INVARIANT: sorted from lowest to highest weight! Except in set reduction operation!

	AggProp const * type;

	agglist aggregates; //OWNS the pointers
	AggPropagator* prop; //OWNS pointer

	int setid;

	bool usingwatches;

	std::map<Atom, AggReason*> reasons;

private:
	void addAgg(const TempAgg& tempagg, bool optim);

public:
	TypedSet(PCSolver* solver, int setid, AggProp const * const w, const vwl& wls, bool usewatches,
			const std::vector<TempAgg*>& aggr, bool optim);
	virtual ~TypedSet();

	// Propagator methods
	virtual rClause getExplanation(const Lit&);
	virtual void accept(ConstraintVisitor&);
	virtual void notifyNewDecisionLevel() {
		throw idpexception("Error in execution path.");
	}
	// NOTE: call explicitly when using hasnextprop/nextprop!
	virtual void notifyBacktrack(int untillevel, const Lit& decision);
	virtual rClause notifypropagate();
	virtual rClause notifyFullAssignmentFound();
	virtual int getNbOfFormulas() const {
		return getWL().size() == 0 ? 0 : getWL().size() * log((double) getWL().size()) / log(2) * getAgg().size();
	}

	// additional
	rClause notifySolver(AggReason* ar);
	void notifypropagate(Watch* w);

	// Getters
	int getSetID() const {
		return setid;
	}
	const vwl& getWL() const {
		return wl;
	}
	const std::vector<Agg*>& getAgg() const {
		return aggregates;
	}
	std::vector<Agg*>& getAggNonConst() {
		return aggregates;
	}
	bool isUsingWatches() const {
		return usingwatches;
	}

	const AggProp& getType() const {
		MAssert(type!=NULL);
		return *type;
	}
	AggProp const * getTypep() const {
		return type;
	}
	AggPropagator* getProp() const {
		return prop;
	}

	// Setters
	void setWL(const vwl& wl2) {
		wl = wl2;
		stable_sort(wl.begin(), wl.end(), compareByWeights<WL>);
	}
	void removeAggs(const std::set<Agg*>& del);

private:
	std::vector<int> backtrack; // The levels for which backtracking the propagator is necessary when we backtrack over them
public:
	void acceptForBacktrack();

private:
	void addExplanation(AggReason& ar) const;
};

void makeSumSetPositive(TypedSet& set);

} /* namespace MinisatID */
#endif /* AGGSET_HPP_ */
