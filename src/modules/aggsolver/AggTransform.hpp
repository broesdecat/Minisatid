/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef AGGTRANSFORM_HPP_
#define AGGTRANSFORM_HPP_

#include <vector>
#include "modules/aggsolver/AggProp.hpp"
#include "modules/aggsolver/AggSet.hpp"
#include "modules/aggsolver/AggUtils.hpp"
#include "theorysolvers/PCSolver.hpp"

namespace MinisatID{

void verifySet(const InnerWLSet& set);

void verifyAggregate(InnerWLSet const * const set, Var head, AggType aggtype);

//@pre: has been split
void setReduce(PCSolver* solver, InnerWLSet* set, std::vector<Agg*>& aggs, const AggProp& type, Weight& knownbound, bool& unsat, bool& sat);
void addHeadImplications(PCSolver* solver, InnerWLSet* set, std::vector<Agg*>& aggs, bool& unsat, bool& sat);
void max2SAT(PCSolver* solver, InnerWLSet* set, std::vector<Agg*>& aggs, bool& unsat, bool& sat);
void card2Equiv(PCSolver* solver, InnerWLSet* set, std::vector<Agg*>& aggs, const Weight& knownbound, bool& unsat, bool& sat);

}

#endif /* AGGTRANSFORM_HPP_ */
