/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef AGG2SAT_HPP_
#define AGG2SAT_HPP_

#include <vector>
#include <algorithm>

#include "modules/aggsolver/AggProp.hpp"
#include "modules/aggsolver/AggSet.hpp"
#include "modules/aggsolver/AggUtils.hpp"
#include "theorysolvers/PCSolver.hpp"
#include "modules/aggsolver/PartiallyWatched.hpp"

#include "PbSolver.h"

namespace MinisatID{

//Temporary structure to create pseudo booleans
struct PBAgg {
	MiniSatPP::vec<MiniSatPP::Lit> literals;
	MiniSatPP::vec<MiniSatPP::Int> weights;
	Weight bound;
	int sign;
};

// FIXME currently, at most one call to execute is allowed, subsequent ones will segfault
class AggToCNFTransformer{
public:
	PCSolver& pcsolver;
	std::vector<PBAgg*> pbaggs;
	int maxvar;

	AggToCNFTransformer(PCSolver* pcsolver):pcsolver(*pcsolver), maxvar(1){}

	void add(InnerWLSet* set, std::vector<TempAgg*>& aggs){
		tempagglist remaining;
		for (auto i=aggs.cbegin(); i!=aggs.cend(); ++i) {
			TempAgg* agg = *i;

			if((agg->getType()!=SUM && agg->getType()!=CARD) || agg->getSem() != COMP){
				// TODO allow complete translation into sat? => double bounds
				remaining.push_back(agg);
				continue;
			}

			PBAgg* ppbaggeq = new PBAgg();
			PBAgg* ppbaggineq = new PBAgg();
			pbaggs.push_back(ppbaggeq);
			pbaggs.push_back(ppbaggineq);
			PBAgg& pbaggeq = *ppbaggeq;
			PBAgg& pbaggineq = *ppbaggineq;
			Weight bound = agg->getBound();
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

	SATVAL execute(){
		MiniSatPP::PbSolver* pbsolver = new MiniSatPP::PbSolver();
		MiniSatPP::opt_verbosity = pcsolver.verbosity()-1; //Gives a bit too much output on 1
		MiniSatPP::opt_abstract = true; //Should be true
		MiniSatPP::opt_tare = true; //Experimentally set to true
		MiniSatPP::opt_primes_file = pcsolver.modes().getPrimesFile().c_str();
		MiniSatPP::opt_convert_weak = false;
		MiniSatPP::opt_convert = MiniSatPP::ct_BDDs;
		pbsolver->allocConstrs(maxvar, pbaggs.size());

		bool unsat = false;
		for (auto i = pbaggs.cbegin(); !unsat && i < pbaggs.cend(); ++i) {
			unsat = !pbsolver->addConstr((*i)->literals, (*i)->weights, MiniSatPP::Int((*i)->bound), (*i)->sign, false);
		}
		deleteList<PBAgg> (pbaggs);

		if (unsat) {
			delete pbsolver;
			deleteList<PBAgg>(pbaggs);
			return SATVAL::UNSAT;
		}

		//get CNF out of the pseudoboolean matrix
		std::vector<std::vector<MiniSatPP::Lit> > pbencodings;
		unsat = !pbsolver->toCNF(pbencodings);
		delete pbsolver;
		if (unsat) {
			deleteList<PBAgg>(pbaggs);
			return SATVAL::UNSAT;
		}

		//Any literal that is larger than maxvar will have been newly introduced, so should be mapped to nVars()+lit
		//add the CNF to the solver
		int maxnumber = pcsolver.nVars();
		for (auto i = pbencodings.cbegin(); i < pbencodings.cend(); ++i) {
			InnerDisjunction clause;
			for (auto j = (*i).cbegin(); j < (*i).cend(); ++j) {
				Var v = MiniSatPP::var(*j) + (MiniSatPP::var(*j) > maxvar ? maxnumber - maxvar : 0);
				clause.literals.push_back(MiniSatPP::sign(*j)?mkNegLit(v):mkPosLit(v));
			}
			pcsolver.add(clause);
		}

		deleteList<PBAgg>(pbaggs);
		return pcsolver.satState();
	}
};

}

#endif /* AGG2SAT_HPP_ */
