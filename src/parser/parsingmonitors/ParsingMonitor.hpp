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
private:
	std::ostream& stream;
public:
	ParsingMonitor(std::ostream& stream): stream(stream){}
	virtual ~ParsingMonitor(){}

	virtual void notifyStart(){}
	virtual void notifyEnd(){}

	virtual void notifyadded(const InnerDisjunction&){}
	virtual void notifyadded(const InnerRule&){}
	virtual void notifyadded(const InnerWLSet&){}
	virtual void notifyadded(const InnerAggregate&){}
	virtual void notifyadded(const InnerReifAggregate&){}
	virtual void notifyadded(const InnerMinimizeOrderedList&){}
	virtual void notifyadded(const InnerMinimizeSubset&){}
	virtual void notifyadded(const InnerMinimizeVar&){}
	virtual void notifyadded(const InnerMinimizeAgg&){}
	virtual void notifyadded(const InnerSymmetry&){}
	virtual void notifyadded(const InnerSymmetryLiterals&){}
	virtual void notifyadded(const InnerForcedChoices&){}
	virtual void notifyadded(const InnerIntVarEnum&){}
	virtual void notifyadded(const InnerIntVarRange&){}
	virtual void notifyadded(const InnerCPAllDiff&){}
	virtual void notifyadded(const InnerCPBinaryRel&){}
	virtual void notifyadded(const InnerCPCount&){}
	virtual void notifyadded(const InnerCPBinaryRelVar&){}
	virtual void notifyadded(const InnerCPSumWeighted&){}

protected:
	std::ostream& target() { return stream; }
};
}

#endif /* PARSINGMONITOR_HPP_ */
