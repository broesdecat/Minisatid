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

class LazyClauseMonitor{
private:
	int residual;
	typedef cb::Callback1<void, const int&> callbackgrounding;
	callbackgrounding requestGroundingCB;

public:
	LazyClauseMonitor(const int& residual):residual(residual){}

	void setRequestMoreGrounding(callbackgrounding cb){
		requestGroundingCB = cb;
	}

	void requestMoreGrounding(){
		requestGroundingCB(residual);
	}
};

// POCO's

class LazyClause{
public:
	Literal residual;
	LazyClauseMonitor* monitor;

	LazyClause(Literal residual, LazyClauseMonitor* monitor)
			:residual(residual), monitor(monitor){}
};

}

#endif /* LAZYCLAUSESUPPORT_HPP_ */
