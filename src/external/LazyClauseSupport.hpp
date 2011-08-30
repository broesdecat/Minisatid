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
	cb::Callback0<bool> requestGroundingCB;
	cb::Callback1<void, LazyClauseRef*> notifyCreated;

public:
	void setRequestMoreGrounding(cb::Callback0<bool> cb){
		requestGroundingCB = cb;
	}

	bool requestMoreGrounding(){
		return requestGroundingCB();
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
	void notifyCertainlyTrue();
	void notifyCertainlyFalse();

	LazyClausePropagator* getClause() const { return clause; }

	LazyClauseRef(LazyClausePropagator * const prop): clause(prop){}
};

// POCO's

class LazyClause{
public:
	Literal tseitin, first, second;
	LazyClauseMonitor* monitor;

	LazyClause(Literal tseitin, Literal first, Literal second, LazyClauseMonitor* monitor)
			:tseitin(tseitin), first(first), second(second), monitor(monitor){}
};

class LazyClauseAddition{
public:
	Literal addedlit;
	LazyClauseRef* ref;

	LazyClauseAddition(Literal lit, LazyClauseRef* ref)
			:addedlit(lit), ref(ref){}
};

}

#endif /* LAZYCLAUSESUPPORT_HPP_ */
