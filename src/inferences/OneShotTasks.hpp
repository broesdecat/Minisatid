/************************************
	OneShotTasks.hpp
	this file belongs to GidL 2.0
	(c) K.U.Leuven
************************************/

#ifndef ONESHOTTASKS_HPP_
#define ONESHOTTASKS_HPP_

#include "Tasks.hpp"
#include "external/Remapper.hpp"
#include "external/Datastructures.hpp"
#include "external/ConstraintAdditionInterface.hpp"
#include "constraintvisitors/FlatZincRewriter.hpp"
#include <typeinfo>

namespace MinisatID{

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

class OneShotFlatzinc: public Task, public FlatZincRewriter<std::ostream>, public ConstraintAdditionInterface<OneShotFlatzinc>{
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
	SearchEngine* getEngine();

	bool isSat() const;
	bool isUnsat() const;
	void notifySolvingAborted();

	void innerExecute();
};

}



#endif /* ONESHOTTASKS_HPP_ */
