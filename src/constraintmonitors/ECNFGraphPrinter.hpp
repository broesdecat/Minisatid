/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef ECNFGRAPHPARSINGMONITOR_HPP_
#define ECNFGRAPHPARSINGMONITOR_HPP_

#include "ConstraintAdditionMonitor.hpp"
#include "utils/Utils.hpp"

namespace MinisatID {

template<typename Stream>
class ECNFGraphPrinter: public ConstraintAdditionMonitor<Stream> {
private:
	using ConstraintAdditionMonitor<Stream>::target;
public:
	ECNFGraphPrinter(Stream& stream) :
			ConstraintAdditionMonitor<Stream>(stream) {
	}
	virtual ~ECNFGraphPrinter() {
	}

	virtual void notifyStart() {
		target() << "graph ecnftheory {\n";
	}
	virtual void notifyEnd() {
		target() << "}\n";
		target().flush();
	}

	void notifyadded(const InnerDisjunction& lits) {
		for (uint i = 0; i < lits.literals.size(); ++i) {
			if (i > 0) {
				target() << " -- ";
			}
			target() << getPrintableVar(var(lits.literals[i]));
		}
		if (lits.literals.size() > 1) {
			target() << " -- " << getPrintableVar(var(lits.literals[0])) << " ";
		}
		target() << "[color=blue];\n";
	}

	void notifyadded(const InnerRule& lits) {
		for (uint i = 0; i < lits.body.size(); ++i) {
			if (i > 0) {
				target() << " -- ";
			}
			target() << getPrintableVar(var(lits.body[i]));
		}
		if (lits.body.size() > 1) {
			target() << " -- " << getPrintableVar(var(lits.body[0])) << " ";
		}
		target() << "[color=green];\n";
	}

	void notifyadded(const InnerWLSet& set) {
		for (unsigned int i = 0; i < set.wls.size(); ++i) {
			if (i > 0) {
				target() << " -- ";
			}
			target() << getPrintableVar(var(set.wls[i].getLit()));
		}
		if (set.wls.size() > 1) {
			target() << " -- " << getPrintableVar(var(set.wls[0].getLit())) << " ";
		}
		target() << "[color=green];\n";
	}

	void notifyadded(const InnerAggregate&) {
		throw idpexception("Not yet implemented."); // TODO
	}
	void notifyadded(const InnerReifAggregate&) {
		throw idpexception("Not yet implemented."); // TODO
	}
	void notifyadded(const InnerMinimizeOrderedList&) {
		throw idpexception("Not yet implemented."); // TODO
	}
	void notifyadded(const InnerMinimizeSubset&) {
		throw idpexception("Not yet implemented."); // TODO
	}
	void notifyadded(const InnerMinimizeAgg&) {
		throw idpexception("Not yet implemented."); // TODO
	}
	void notifyadded(const InnerMinimizeVar&) {
		throw idpexception("Not yet implemented."); // TODO
	}
	void notifyadded(const InnerSymmetry&) {
		throw idpexception("Not yet implemented."); // TODO
	}
	void notifyadded(const InnerForcedChoices&) {
		throw idpexception("Not yet implemented."); // TODO
	}
	void notifyadded(const InnerIntVarRange&) {
		throw idpexception("Not yet implemented."); // TODO
	}
	void notifyadded(const InnerIntVarEnum&) {
		throw idpexception("Not yet implemented."); // TODO
	}
	void notifyadded(const InnerCPAllDiff&) {
		throw idpexception("Not yet implemented."); // TODO
	}
	void notifyadded(const InnerCPBinaryRel&) {
		throw idpexception("Not yet implemented."); // TODO
	}
	void notifyadded(const InnerCPCount&) {
		throw idpexception("Not yet implemented."); // TODO
	}
	void notifyadded(const InnerCPBinaryRelVar&) {
		throw idpexception("Not yet implemented."); // TODO
	}
	void notifyadded(const InnerCPSumWeighted&) {
		throw idpexception("Not yet implemented."); // TODO
	}
};

}

#endif /* ECNFGRAPHPARSINGMONITOR_HPP_ */
