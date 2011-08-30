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
	int id;
	cb::Callback0<bool> requestGroundingCB;
	cb::Callback2<void, int, LazyClauseRef*> notifyCreated;

public:
	LazyClauseMonitor(int id): id(id){}

	void setRequestMoreGrounding(cb::Callback0<bool> cb){
		requestGroundingCB = cb;
	}

	bool requestMoreGrounding(){
		return requestGroundingCB();
	}

	void setNotifyClauseCreated(cb::Callback2<void, int, LazyClauseRef*> cb){
		notifyCreated = cb;
	}

	void notifyClauseCreated(LazyClauseRef* ref){
		notifyCreated(id, ref);
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
	Literal tseitin, first;
	LazyClauseMonitor* monitor;

	LazyClause(Literal tseitin, Literal first, LazyClauseMonitor* monitor)
			:tseitin(tseitin), first(first), monitor(monitor){}
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
