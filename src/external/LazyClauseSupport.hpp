/************************************
	LazyClauseSupport.hpp
	this file belongs to GidL 2.0
	(c) K.U.Leuven
************************************/

#ifndef LAZYCLAUSESUPPORT_HPP_
#define LAZYCLAUSESUPPORT_HPP_

#include "callback.hpp"

#include "external/Datastructures.hpp"

namespace MinisatID{

class LazyClausePropagator;
class LazyClauseRef;

class LazyGroundingCommand{
public:
	LazyGroundingCommand(){}
	virtual void requestGrounding() = 0;
};

// POCO's

class LazyGroundLit{
public:
	bool watchboth;
	Literal residual;
	LazyGroundingCommand* monitor;

	LazyGroundLit(bool watchboth, const Literal& residual, LazyGroundingCommand* monitor)
			:watchboth(watchboth), residual(residual), monitor(monitor){}
};

}

#endif /* LAZYCLAUSESUPPORT_HPP_ */
