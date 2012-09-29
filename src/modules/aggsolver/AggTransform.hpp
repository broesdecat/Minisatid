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

void verifySet(const WLSet& set, AggType type);

class PCSolver;
void verifyAggregate(WLSet const * const set, AggType settype, const Lit& head, AggType aggtype, const PCSolver& solver);

//@pre: has been split
void setReduce(PCSolver* solver, WLSet* set, const AggProp& type);
void addHeadImplications(PCSolver* solver, WLSet* set, std::vector<TempAgg*>& aggs, bool& unsat, bool& sat);
void max2SAT(PCSolver* solver, WLSet* set, std::vector<TempAgg*>& aggs, bool& unsat, bool& sat);
void card2Equiv(PCSolver* solver, WLSet* set, std::vector<TempAgg*>& aggs, bool& unsat, bool& sat);
void decideUsingWatchesAndCreatePropagators(PCSolver* solver, WLSet* set, const std::vector<TempAgg*>& aggs);
void decideUsingWatchesAndCreateMinimizationPropagator(PCSolver* solver, WLSet* set, TempAgg*, uint priority);

}

#endif /* AGGTRANSFORM_HPP_ */
