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

	virtual void notifyadded(const InnerDisjunction& lits){}
	virtual void notifyadded(const InnerRule& lits){}
	virtual void notifyadded(const InnerWLSet& lits){}
	virtual void notifyadded(const InnerAggregate& lits){}
	virtual void notifyadded(const InnerReifAggregate& lits){}
	virtual void notifyadded(const InnerMinimizeOrderedList& set){}
	virtual void notifyadded(const InnerMinimizeSubset& set){}
	virtual void notifyadded(const InnerMinimizeVar& set){}
	virtual void notifyadded(const InnerMinimizeAgg& set){}
	virtual void notifyadded(const InnerSymmetry& set){}
	virtual void notifyadded(const InnerSymmetryLiterals& set){}
	virtual void notifyadded(const InnerForcedChoices& set){}
	virtual void notifyadded(const InnerIntVarEnum& set){}
	virtual void notifyadded(const InnerIntVarRange& set){}
	virtual void notifyadded(const InnerCPAllDiff& set){}
	virtual void notifyadded(const InnerCPBinaryRel& set){}
	virtual void notifyadded(const InnerCPCount& set){}
	virtual void notifyadded(const InnerCPBinaryRelVar& set){}
	virtual void notifyadded(const InnerCPSumWeighted& set){}

protected:
	std::ostream& target() { return stream; }
};
}

#endif /* PARSINGMONITOR_HPP_ */
