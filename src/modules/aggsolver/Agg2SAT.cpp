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
Lit mapFromPBLit(MiniSatPP::Lit lit, int maxopbvar, PCSolver& pcsolver, std::map<Atom, Atom>& opbinternal2pcsolver){
	auto var = MiniSatPP::var(lit);
	if(var <= maxopbvar){
		return mkLit(var, sign(lit));
	}else{
		auto it = opbinternal2pcsolver.find(var);
		if(it==opbinternal2pcsolver.cend()){
			auto newv = pcsolver.newAtom();
			opbinternal2pcsolver[var] = newv;
			var = newv;
		}else{
			var = it->second;
		}
		return mkLit(var, sign(lit));
	}
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
		for (auto wlt : set->getWL()) {
			pbaggeq->literals.push(mapToPBLit(wlt.getLit()));
			pbaggineq->literals.push(mapToPBLit(wlt.getLit()));
			if (var(wlt.getLit()) > maxvar) {
				maxvar = var(wlt.getLit());
			}
			if (wlt.getWeight() < 0) {
				min += wlt.getWeight();
			} else {
				max += wlt.getWeight();
			}
			pbaggeq->weights.push(MiniSatPP::Int(toInt(wlt.getWeight())));  // FIXME use the bignums without downcast? (5 places in file)
			pbaggineq->weights.push(MiniSatPP::Int(toInt(wlt.getWeight())));
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

template<class ListTo, class ListFrom>
void addAll(const ListFrom& from, ListTo& to){
	to.insert(to.end(), from.cbegin(), from.cend());
}

SATVAL MinisatID::execute(AggToCNFTransformer& transformer) {
	auto& pcsolver = transformer.pcsolver;
	MiniSatPP::PBOptions options;
	options.opt_verbosity = pcsolver.verbosity() - 1; //Gives a bit too much output on 1
	options.opt_abstract = true; //Should be true
	options.opt_tare = true; //Experimentally set to true
	options.opt_convert_weak = false;
	options.opt_convert = MiniSatPP::ct_Adders;
	auto pbsolver = new MiniSatPP::PbSolver(pcsolver.modes().getPrimesFile(), &options);
	pbsolver->allocConstrs(transformer.maxvar, transformer.pbaggs.size());

	bool unsat = false;
	for(auto agg:transformer.pbaggs){
		unsat = !pbsolver->addConstr(agg->literals, agg->weights, MiniSatPP::Int(toInt(agg->bound)), agg->sign, false);
		if(unsat){
			break;
		}
	}

	if (unsat) {
		delete pbsolver;
		return SATVAL::UNSAT;
	}

	//get CNF out of the pseudoboolean matrix
	std::vector<std::vector<MiniSatPP::Lit> > pbencodings;
	unsat = not pbsolver->toCNF(pbencodings);
	delete pbsolver;
	if (unsat) {
		return SATVAL::UNSAT;
	}

	//add the CNF to the solver
	for (auto enc : pbencodings) {
		Disjunction clause({});
		for (auto pbl : enc) {
			clause.literals.push_back(mapFromPBLit(pbl, transformer.maxvar, pcsolver, transformer.opbinternal2pcsolver));
		}
		internalAdd(clause, pcsolver.getTheoryID(), pcsolver);
	}

	return pcsolver.satState();
}
