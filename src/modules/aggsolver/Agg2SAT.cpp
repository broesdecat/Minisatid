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

#include "Agg2SAT.hpp"

#include "AggProp.hpp"
#include "AggSet.hpp"
#include "AggUtils.hpp"
#include "PartiallyWatched.hpp"

#include "theorysolvers/PCSolver.hpp"

#include "PbSolver.h"

using namespace MinisatID;

//Temporary structure to create pseudo booleans
struct MinisatID::PBAgg {
	MiniSatPP::vec<MiniSatPP::Lit> literals;
	MiniSatPP::vec<MiniSatPP::Int> weights;
	Weight bound;
	int sign;
};

AggToCNFTransformer::~AggToCNFTransformer(){
	deleteList<PBAgg>(pbaggs);
}

void AggToCNFTransformer::add(InnerWLSet* set, std::vector<TempAgg*>& aggs) {
	tempagglist remaining;
	for (auto i = aggs.cbegin(); i != aggs.cend(); ++i) {
		TempAgg* agg = *i;

		if ((agg->getType() != AggType::SUM && agg->getType() != AggType::CARD) || agg->getSem() != AggSem::COMP) {
			// TODO allow complete translation into sat? => double bounds
			remaining.push_back(agg);
			continue;
		}

		auto ppbaggeq = new PBAgg();
		auto ppbaggineq = new PBAgg();
		pbaggs.push_back(ppbaggeq);
		pbaggs.push_back(ppbaggineq);
		auto& pbaggeq = *ppbaggeq;
		auto& pbaggineq = *ppbaggineq;
		auto bound = agg->getBound();
		if (agg->hasUB()) {
			pbaggeq.sign = -1;
			pbaggineq.sign = 2;
		} else {
			pbaggeq.sign = 1;
			pbaggineq.sign = -2;
		}
		pbaggeq.bound = bound;
		pbaggineq.bound = bound;
		Weight min = 0, max = 0;
		for (auto k = set->getWL().cbegin(); k < set->getWL().cend(); ++k) {
			pbaggeq.literals.push(MiniSatPP::Lit(var((*k).getLit()), sign((*k).getLit())));
			pbaggineq.literals.push(MiniSatPP::Lit(var((*k).getLit()), sign((*k).getLit())));
			if (var((*k).getLit()) > maxvar) {
				maxvar = var((*k).getLit());
			}
			if ((*k).getWeight() < 0) {
				min += (*k).getWeight();
			} else {
				max += (*k).getWeight();
			}
			pbaggeq.weights.push(MiniSatPP::Int((*k).getWeight()));
			pbaggineq.weights.push(MiniSatPP::Int((*k).getWeight()));
		}
		if (var(agg->getHead()) > maxvar) {
			maxvar = var(agg->getHead());
		}
		pbaggeq.literals.push(MiniSatPP::Lit(var(agg->getHead()), true));
		pbaggineq.literals.push(MiniSatPP::Lit(var(agg->getHead()), false));
		Weight eqval, ineqval;
		if (agg->hasUB()) {
			eqval = -abs(bound) - abs(max) - 1;
			ineqval = abs(bound) + abs(min) + 1;
		} else {
			eqval = abs(bound) + abs(min) + 1;
			ineqval = -abs(bound) - abs(max) - 1;
		}
		pbaggeq.weights.push(MiniSatPP::Int(eqval));
		pbaggineq.weights.push(MiniSatPP::Int(ineqval));
	}
	aggs = remaining;
}

SATVAL MinisatID::execute(const AggToCNFTransformer& transformer) {
	auto pcsolver = transformer.pcsolver;
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
		unsat = !pbsolver->addConstr((*i)->literals, (*i)->weights, MiniSatPP::Int((*i)->bound), (*i)->sign, false);
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

	//Any literal that is larger than maxvar will have been newly introduced, so should be mapped to nVars()+lit
	//add the CNF to the solver
	int maxnumber = pcsolver.nVars();
	for (auto i = pbencodings.cbegin(); i < pbencodings.cend(); ++i) {
		InnerDisjunction clause;
		for (auto j = (*i).cbegin(); j < (*i).cend(); ++j) {
			Var v = MiniSatPP::var(*j) + (MiniSatPP::var(*j) > transformer.maxvar ? maxnumber - transformer.maxvar : 0);
			clause.literals.push_back(MiniSatPP::sign(*j) ? mkNegLit(v) : mkPosLit(v));
		}
		pcsolver.add(clause);
	}

	return pcsolver.satState();
}
