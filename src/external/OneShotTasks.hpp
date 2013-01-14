/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef ONESHOTTASKS_HPP_
#define ONESHOTTASKS_HPP_

#include "Tasks.hpp"
#include "Datastructures.hpp"
#include "ConstraintAdditionInterface.hpp"
#include <typeinfo>
#include <unordered_set>

namespace MinisatID{

template<class T> class FlatZincRewriter;

class OneShotUnsatCoreExtraction: public Task, public ExternalConstraintVisitor{
private:
	std::map<constraint_id, ID*> id2constr;
	std::map<Atom, std::vector<constraint_id> > marker2ids;
	std::vector<Lit> markerAssumptions; // Note: internal literals
	Space* space;
	std::unique_ptr<ModelExpand> mx;
	std::unique_ptr<ModelExpandOptions> mxopts;
	std::vector<constraint_id> unsatcore;

public:
	using ExternalConstraintVisitor::add;
	
	virtual void add(const Disjunction&);
	virtual void add(const WLSet&);
	virtual void add(const Aggregate&);
	virtual void add(const Rule&);
	
	void innerExecute();

	OneShotUnsatCoreExtraction(const SolverOption& options);
	~OneShotUnsatCoreExtraction();

	std::vector<constraint_id> getUnsatCoreIDs() const{
		return unsatcore;
	}

	OneShotUnsatCoreExtraction* getEngine() const { return const_cast<OneShotUnsatCoreExtraction*>(this); } // TODO Ugly const cast?
};

}

#endif /* ONESHOTTASKS_HPP_ */
