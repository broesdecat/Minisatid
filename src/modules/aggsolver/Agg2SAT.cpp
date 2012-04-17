/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */

#include <vector>
#include <algorithm>
#include <iostream>

#include "Agg2SAT.hpp"

#include "AggProp.hpp"
#include "AggSet.hpp"
#include "AggUtils.hpp"
#include "PartiallyWatched.hpp"

#include "theorysolvers/PCSolver.hpp"
#include "datastructures/InternalAdd.hpp"
#include "external/utils/ContainerUtils.hpp"

#include "PbSolver.h"

using namespace MinisatID;

//Temporary structure to create pseudo booleans
struct MinisatID::PBAgg {
	MiniSatPP::vec<MiniSatPP::Lit> literals;
	MiniSatPP::vec<MiniSatPP::Int> weights;
	Weight bound;
	int sign;
};

AggToCNFTransformer::~AggToCNFTransformer() {
	deleteList<PBAgg>(pbaggs);
}

MiniSatPP::Lit mapToPBLit(Lit lit){
	return MiniSatPP::Lit(var(lit), sign(lit));
}

//Any literal that is larger than maxvar was newly introduced by the transformation, so should be mapped to nVars()+lit
Lit mapFromPBLit(MiniSatPP::Lit lit, int maxopbvar, int nvars){
	auto v = MiniSatPP::var(lit) + (MiniSatPP::var(lit) > maxopbvar ? nvars - maxopbvar: 0);
	return mkLit(v, sign(lit));
}

void AggToCNFTransformer::add(WLSet* set, std::vector<TempAgg*>& aggs) {
	tempagglist remaining;
	for (auto i = aggs.cbegin(); i != aggs.cend(); ++i) {
		TempAgg* agg = *i;

		if ((agg->getType() != AggType::SUM && agg->getType() != AggType::CARD) || agg->getSem() != AggSem::COMP) {
			// TODO allow complete translation into sat? => double bounds
			remaining.push_back(agg);
			continue;
		}

		auto pbaggeq = new PBAgg();
		auto pbaggineq = new PBAgg();
		auto bound = agg->getBound();
		pbaggeq->bound = bound;
		pbaggineq->bound = bound;
		if (agg->hasUB()) {
			pbaggeq->sign = -1;
			pbaggineq->sign = 1;
			pbaggineq->bound+=Weight(1); // Strictly larger than
		} else {
			pbaggineq->sign = -1;
			pbaggineq->bound-=Weight(1); // Strictly lower than
			pbaggeq->sign = 1;
		}
		Weight min = 0, max = 0;
		for (auto k = set->getWL().cbegin(); k < set->getWL().cend(); ++k) {
			pbaggeq->literals.push(mapToPBLit((*k).getLit()));
			pbaggineq->literals.push(mapToPBLit((*k).getLit()));
			if (var((*k).getLit()) > maxvar) {
				maxvar = var((*k).getLit());
			}
			if ((*k).getWeight() < 0) {
				min += (*k).getWeight();
			} else {
				max += (*k).getWeight();
			}
			pbaggeq->weights.push(MiniSatPP::Int(toInt((*k).getWeight())));  // FIXME use the bignums without downcast? (5 places in file)
			pbaggineq->weights.push(MiniSatPP::Int(toInt((*k).getWeight())));
		}
		auto headval = pcsolver.rootValue(agg->getHead());
		if (headval == l_Undef) {
			pbaggeq->literals.push(mapToPBLit(~agg->getHead()));
			pbaggineq->literals.push(mapToPBLit(agg->getHead()));
			if (var(agg->getHead()) > maxvar) {
				maxvar = var(agg->getHead());
			}
			Weight eqval, ineqval;
			if (agg->hasUB()) {
				ineqval = abs(pbaggineq->bound) + abs(min) + 1;
				eqval = -abs(pbaggeq->bound) - abs(max) - 1;
			} else {
				eqval = abs(pbaggeq->bound) + abs(min) + 1;
				ineqval = -abs(pbaggineq->bound) - abs(max) - 1;
			}
			pbaggeq->weights.push(MiniSatPP::Int(toInt(eqval)));
			pbaggineq->weights.push(MiniSatPP::Int(toInt(ineqval)));
		}
		if (headval != l_False) {
			pbaggs.push_back(pbaggeq);
		}
		if (headval != l_True) {
			pbaggs.push_back(pbaggineq);
		}

		/**
		 * Doel voor H <=> set >= n
		 * H => set >= n
		 * ~H => set < n
		 *
		 * richting 1: H true moet zich gedragen als  set >= n
		 * 				H false moet triviaal true zijn
		 * 					dus set + (n+abs minwaarde)*~H >= n
		 * 	richting 2: H false moet zich gedragen als set < n
		 * 				H true moet triviaal true zijn
		 * 					dus set + (-n-abs max)*H < n of dus =< n-1
		 */

	}
	aggs = remaining;
}

SATVAL MinisatID::execute(const AggToCNFTransformer& transformer) {
	auto& pcsolver = transformer.pcsolver;
	auto pbsolver = new MiniSatPP::PbSolver();
	MiniSatPP::opt_verbosity = pcsolver.verbosity() - 1; //Gives a bit too much output on 1
	MiniSatPP::opt_abstract = true; //Should be true
	MiniSatPP::opt_tare = true; //Experimentally set to true
	MiniSatPP::opt_primes_file = pcsolver.modes().getPrimesFile().c_str();
	MiniSatPP::opt_convert_weak = false;
	MiniSatPP::opt_convert = MiniSatPP::ct_BDDs;
	pbsolver->allocConstrs(transformer.maxvar, transformer.pbaggs.size());

	bool unsat = false;
	for (auto i = transformer.pbaggs.cbegin(); !unsat && i < transformer.pbaggs.cend(); ++i) {
		unsat = !pbsolver->addConstr((*i)->literals, (*i)->weights, MiniSatPP::Int(toInt((*i)->bound)), (*i)->sign, false);
	}

	if (unsat) {
		delete pbsolver;
		return SATVAL::UNSAT;
	}

	//get CNF out of the pseudoboolean matrix
	std::vector<std::vector<MiniSatPP::Lit> > pbencodings;
	unsat = !pbsolver->toCNF(pbencodings);
	delete pbsolver;
	if (unsat) {
		return SATVAL::UNSAT;
	}

	//add the CNF to the solver
	int maxnumber = pcsolver.nVars();
	for (auto i = pbencodings.cbegin(); i < pbencodings.cend(); ++i) {
		Disjunction clause;
		for (auto j = (*i).cbegin(); j < (*i).cend(); ++j) {
			clause.literals.push_back(mapFromPBLit(*j, transformer.maxvar, maxnumber));
		}
		add(clause, pcsolver);
	}

	return pcsolver.satState();
}
