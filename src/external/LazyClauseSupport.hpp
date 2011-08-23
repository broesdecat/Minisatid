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
	cb::Callback0<void> requestGroundingCB;
	cb::Callback1<void, LazyClauseRef*> notifyCreated;

public:
	void setRequestMoreGrounding(cb::Callback0<void> cb){
		requestGroundingCB = cb;
	}

	void requestMoreGrounding(){
		requestGroundingCB();
	}

	void setNotifyClauseCreated(cb::Callback1<void, LazyClauseRef*> cb){
		notifyCreated = cb;
	}

	void notifyClauseCreated(LazyClauseRef* ref){
		notifyCreated(ref);
	}
};
class LazyClauseRef{
private:
	LazyClausePropagator* clause;

public:
	void notifyFullyGrounded();
	void notifyCertainlyTrue();
	void notifyCertainlyFalse();
};

class LazyClause{
public:
	LazyClauseMonitor* monitor;
	Literal tseitin;

	LazyClause(Literal tseitin, LazyClauseMonitor* monitor)
			:tseitin(tseitin), monitor(monitor){}
};

class LazyClauseAddition{
public:
	LazyClauseRef* ref;
	Literal addedlit;

	LazyClauseAddition(Literal lit, LazyClauseRef* ref)
			:addedlit(lit), ref(ref){}
};

}

#endif /* LAZYCLAUSESUPPORT_HPP_ */
