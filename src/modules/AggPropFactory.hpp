/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef AggSolver_H_
#define AggSolver_H_

#include <cstdio>
#include <map>
#include <set>

#include "modules/aggsolver/AggUtils.hpp"

namespace MinisatID {

class PropagatorFactory;
class PCSolver;
class IDSolver;

class WL;
typedef std::vector<WL> vwl;

class Agg;
class TypedSet;
class Watch;
class AggReason;
struct AggBound;

typedef std::map<int, TypedSet*> setid2set;
typedef std::vector<TypedSet*> setlist;
typedef std::set<Var> varlist;

class AggPropFactory{
private:
	PropagatorFactory* propagatorfactory;

	setid2set 	parsedSets;
	setlist		sets;
	varlist		heads;
	Var 		temphead;
	Lit			dummyhead;

public:
	AggPropFactory(PropagatorFactory* s);
	~AggPropFactory();

	/**
	 * @pre: no set with the same id has already been added
	 * @pre: set is not empty
	 */
	bool addSet(int id, const std::vector<WL>& weightedliterals);
	bool addAggrExpr(const InnerReifAggregate& agg);
	bool addAggrExpr(const InnerAggregate& agg);

	void finishParsing(bool& unsat);

private:
	bool AggPropFactory::addAggrExpr(const InnerReifAggregate& agg);

	const PropagatorFactory& getPropagatorFactory() const { return *propagatorfactory; }
	PropagatorFactory& getPropagatorFactory() { return *propagatorfactory; }
	const PCSolver& getEngine() const;
	PCSolver& getEngine();
	PCSolver* getEnginep();

	bool 		hasIDSolver(int defid) const;
	IDSolver& 	getIDSolver(int defid);
};

}

#endif /* AggSolver_H_ */
