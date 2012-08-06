/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */

#ifndef REALCNFPRINTER_HPP_
#define REALCNFPRINTER_HPP_

#include "external/ConstraintVisitor.hpp"
#include "utils/Utils.hpp"
#include "utils/Print.hpp"

namespace MinisatID {

template<typename Stream>
class RealCNFPrinter: public ConstraintStreamPrinter<Stream> {
private:
	std::stringstream ss;
	int nbconstraints, maxvar;
	using ConstraintStreamPrinter<Stream>::target;
	// NOTE: printing the remapped literals here!
public:
	RealCNFPrinter(LiteralPrinter* solver, Stream& stream) :
		ConstraintStreamPrinter<Stream>(solver, stream, "cnfprinter") {
}
	virtual ~RealCNFPrinter() {
	}

	void notifyStart(){
		nbconstraints = 0;
		maxvar=1;
		ss.str(std::string());
	}
	void notifyEnd(){
		ss <<"p cnf " <<maxvar <<" " <<nbconstraints <<"\n";
		target() <<ss.str();
		target().flush();
	}

	std::string toString(const Lit& lit){
		std::stringstream ss;
		ss <<(sign(lit)?"-":"") <<(var(lit)+1);
		return ss.str();
	}

	void add(const Disjunction& clause) {
		for(auto lit:clause.literals){
			if(maxvar<var(lit)){
				maxvar = var(lit);
			}
			target() <<toString(lit) << " ";
		}
		nbconstraints++;
		target() << "0\n";
	}
};

}

#endif //AREALECNFPRINTER_HPP_
