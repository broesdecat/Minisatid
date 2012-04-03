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

namespace MinisatID{

class OneShotUnsatCoreExtraction: public Task, public ConstraintAdditionInterface<OneShotUnsatCoreExtraction>{
public:
	template<class T>
	void add(const T& formula){

	}

	OneShotUnsatCoreExtraction* getEngine() const { return this; }
};

class OneShotFlatzinc: public Task, public FlatZincRewriter<std::ostream>, public ConstraintAdditionInterface<OneShotUnsatCoreExtraction>{
	template<class T>
	void add(const T& formula){

	}

	OneShotUnsatCoreExtraction* getEngine() const { return this; }
};

}



#endif /* ONESHOTTASKS_HPP_ */
