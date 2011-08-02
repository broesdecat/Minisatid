/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef ECNFPRINTER_HPP_
#define ECNFPRINTER_HPP_

#include <vector>
#include <sstream>
#include <iostream>
#include "utils/Utils.hpp"

namespace MinisatID{

class InnerDisjunction;
class InnerSet;
class InnerWSet;
class Aggregate;

class ECNFPrinter {
private:
	std::stringstream ss;

public:
	ECNFPrinter();
	virtual ~ECNFPrinter();

	void 	startPrinting();
	void 	endPrinting(std::ostream& stream);

	template<class T>
	void 	notifyadded(const T& formula);
};

template<>
void ECNFPrinter::notifyadded(const InnerDisjunction& lits);
template<>
void ECNFPrinter::notifyadded(const InnerRule& lits);
template<>
void ECNFPrinter::notifyadded(const InnerSet& lits);
template<>
void ECNFPrinter::notifyadded(const InnerWSet& lits);
template<>
void ECNFPrinter::notifyadded(const InnerAggregate& lits);
template<>
void ECNFPrinter::notifyadded(const InnerMinimizeAgg& set);
template<>
void ECNFPrinter::notifyadded(const InnerMinimizeOrderedList& set);
template<>
void ECNFPrinter::notifyadded(const InnerMinimizeSubset& set);
template<>
void ECNFPrinter::notifyadded(const InnerSymmetryLiterals& set);
template<>
void ECNFPrinter::notifyadded(const InnerSymmetry& set);
template<>
void ECNFPrinter::notifyadded(const InnerForcedChoices& set);
template<>
void ECNFPrinter::notifyadded(const InnerIntVarEnum& set);
template<>
void ECNFPrinter::notifyadded(const InnerIntVarRange& set);
template<>
void ECNFPrinter::notifyadded(const InnerCPAllDiff& set);
template<>
void ECNFPrinter::notifyadded(const InnerCPBinaryRel& set);
template<>
void ECNFPrinter::notifyadded(const InnerCPCount& set);
template<>
void ECNFPrinter::notifyadded(const InnerCPBinaryRelVar& set);
template<>
void ECNFPrinter::notifyadded(const InnerCPSumWeighted& set);

}
/*
class ECNFGraphPrinter {
private:
	std::stringstream ss;

public:
	ECNFGraphPrinter();
	virtual ~ECNFGraphPrinter();

	void 	startPrinting();
	void 	endPrinting(std::ostream& stream);

	template<class T>
	void 	notifyadded(const T& formula);
};

template<>
void ECNFGraphPrinter::notifyadded(const InnerDisjunction& lits);
template<>
void ECNFGraphPrinter::notifyadded(const InnerWSet& lits);

}*/

#endif /* ECNFPRINTER_HPP_ */
