/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef SCCtoCNF_HPP_
#define SCCtoCNF_HPP_

#include <vector>
#include <cmath>

#include "utils/Utils.hpp"

namespace MinisatID {

class PCSolver;

namespace toCNF{

class Rule{
	bool disjunctive_;
	Var head_;
	std::vector<Var> defbody_;
	std::vector<Lit> openbody_;

public:
	Rule(bool disjunctive, Var head, const std::vector<Var>& deflits, const std::vector<Lit>& openlits)
			:disjunctive_(disjunctive), head_(head), defbody_(deflits), openbody_(openlits){

	}

	Var getHead() const { return head_; }
	bool isDisjunctive() const { return disjunctive_; }
	const std::vector<Var>& defVars() const { return defbody_; }
	const std::vector<Lit>& openLits() const { return openbody_; }
};

bool transformSCCtoCNF(PCSolver& solver, const std::vector<Rule*>& rules);

}

} /* namespace MinisatID */
#endif /* SCCtoCNF_HPP_ */
