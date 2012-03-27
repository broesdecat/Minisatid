/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */

#ifndef REALECNFPRINTER_HPP_
#define REALECNFPRINTER_HPP_

#include "ConstraintAdditionMonitor.hpp"
#include "utils/Utils.hpp"
#include "utils/Print.hpp"

namespace MinisatID {

template<typename Stream>
class RealECNFPrinter: public ConstraintAdditionMonitor<Stream> {
private:
	using ConstraintAdditionMonitor<Stream>::target;
public:
	RealECNFPrinter(Stream& stream) :
			ConstraintAdditionMonitor<Stream>(stream) {
	}
	virtual ~RealECNFPrinter() {
	}

	void notifyStart(){}
	void notifyEnd(){
		target().flush();
	}

	void notifyadded(const InnerDisjunction& clause) {
		for (int i = 0; i < clause.literals.size(); ++i) {
			ss << clause.literals[i] << " ";
		}
		ss << "0\n";
	}

	void notifyadded(const InnerRule& rule) {
		ss << (rule.conjunctive ? "C" : "D") << " " << rule.head << " ";
		for (int i = 0; i < rule.body.size(); ++i) {
			ss << rule.body[i] << " ";
		}
		ss << "0\n";
	}

	void notifyadded(const InnerWSet& set) {
		ss << "WSet " << set.setID << " ";
		for (uint i = 0; i < set.literals.size(); ++i) {
			ss << set.literals[i] << "=" << set.weights[i] << " ";
		}
		ss << "0\n";
	}

	void notifyadded(const InnerReifAggregate& agg) {
		ss << "Added aggregate " << agg.head << " " << (agg.sem == COMP ? "<=>" : "<-");
		if (agg.sem == DEF) {
			ss << "(" << agg.defID << ")";
		}
		ss << " " << agg.type;
		ss << "( set" << agg.setID << " )" << (agg.sign == AGGSIGN_UB ? "=<" : ">=") << agg.bound;
		ss << "\n";
	}
};

}

#endif //REALECNFPRINTER_HPP_
