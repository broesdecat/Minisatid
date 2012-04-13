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
#include "Remapper.hpp"
#include "Datastructures.hpp"
#include "ConstraintAdditionInterface.hpp"
#include <typeinfo>

namespace MinisatID{

template<class T> class FlatZincRewriter;

class OneShotUnsatCoreExtraction: public Task, public ConstraintAdditionInterface<OneShotUnsatCoreExtraction>{
private:
	int maxid;// FIXME temporary
	std::map<int, Var> id2Marker;
	std::vector<Lit> markerAssumptions;
	Space* space;
public:
	template<class T>
	void extAdd(const T& formula){
		std::stringstream ss;
		ss <<"Unsupported constraint type " <<typeid(T).name() <<"encountered in Unsat core extraction.";
		throw idpexception(ss.str());
	}

	void innerExecute();

	OneShotUnsatCoreExtraction(const SolverOption& options);
	~OneShotUnsatCoreExtraction();

	OneShotUnsatCoreExtraction* getEngine() { return this; }
};

template<>
void OneShotUnsatCoreExtraction::extAdd(const Disjunction& disjunction);

class OneShotFlatzinc: public Task, public ConstraintAdditionInterface<OneShotFlatzinc>{
private:
	FlatZincRewriter<std::ostream>* fzrw;
public:
	OneShotFlatzinc* getEngine() { return this; }
};

class Space;
class ModelExpand;

class OneShotMX: public MXTask, public ConstraintAdditionInterface<SearchEngine>{
private:
	bool localspace;
	ModelExpand* mx;
public:
	OneShotMX(SolverOption options, ModelExpandOptions mxoptions, const litlist& assumptions);
	OneShotMX(Space* space, ModelExpandOptions mxoptions, const litlist& assumptions);
	~OneShotMX();
	SearchEngine* getEngine() const;

	bool isSat() const;
	bool isUnsat() const;
	void notifySolvingAborted();

	void innerExecute();
};

}



#endif /* ONESHOTTASKS_HPP_ */
