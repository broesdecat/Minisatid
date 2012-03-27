/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mari�n, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef PARSINGMONITOR_HPP_
#define PARSINGMONITOR_HPP_

#include <iostream>
#include "utils/Print.hpp"
#include "utils/Utils.hpp"

namespace MinisatID{

class ParsingMonitor {
public:
	virtual ~ParsingMonitor(){}

	virtual void notifyStart() = 0;
	virtual void notifyEnd() = 0;

	virtual void notifyadded(const InnerDisjunction&) = 0;
	virtual void notifyadded(const InnerRule&) = 0;
	virtual void notifyadded(const InnerWLSet&) = 0;
	virtual void notifyadded(const InnerAggregate&) = 0;
	virtual void notifyadded(const InnerReifAggregate&) = 0;
	virtual void notifyadded(const InnerMinimizeOrderedList&) = 0;
	virtual void notifyadded(const InnerMinimizeSubset&) = 0;
	virtual void notifyadded(const InnerMinimizeVar&) = 0;
	virtual void notifyadded(const InnerMinimizeAgg&) = 0;
	virtual void notifyadded(const InnerSymmetry&) = 0;
	virtual void notifyadded(const InnerForcedChoices&) = 0;
	virtual void notifyadded(const InnerIntVarEnum&) = 0;
	virtual void notifyadded(const InnerIntVarRange&) = 0;
	virtual void notifyadded(const InnerCPAllDiff&) = 0;
	virtual void notifyadded(const InnerCPBinaryRel&) = 0;
	virtual void notifyadded(const InnerCPCount&) = 0;
	virtual void notifyadded(const InnerCPBinaryRelVar&) = 0;
	virtual void notifyadded(const InnerCPSumWeighted&) = 0;


};

template<typename Stream>
class ConstraintAdditionMonitor: public ParsingMonitor{
private:
	Stream& stream;
public:
	ConstraintAdditionMonitor(Stream& stream): stream(stream){}
protected:
	Stream& target() { return stream; }
};
}

#endif /* PARSINGMONITOR_HPP_ */
