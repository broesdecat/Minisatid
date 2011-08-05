/************************************
	Agg2SAT.hpp
	this file belongs to GidL 2.0
	(c) K.U.Leuven
************************************/

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

//FUTURE allow complete translation into sat? => double bounds
template<class AggSetContainer>
bool transformSumsToCNF(PCSolver& pcsolver, const AggSetContainer& sets) {
	int sumaggs = 0;
	int maxvar = 1;
	std::vector<PBAgg*> pbaggs;
	for (auto i = sets.begin(); i != sets.end(); ++i) {
		TypedSet* set = (*i).second;
		agglist remaining;
		for (vsize j = 0; j < set->getAgg().size(); ++j) {
			Agg* agg = set->getAgg()[j];

			if((agg->getType()!=SUM && agg->getType()!=CARD) || agg->getSem() != COMP){
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
			for (auto k = set->getWL().begin(); k < set->getWL().end(); ++k) {
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
		set->replaceAgg(remaining);
	}

	MiniSatPP::PbSolver* pbsolver = new MiniSatPP::PbSolver();
	MiniSatPP::opt_verbosity = pcsolver.verbosity()-1; //Gives a bit too much output on 1
	MiniSatPP::opt_abstract = true; //Should be true
	MiniSatPP::opt_tare = true; //Experimentally set to true
	MiniSatPP::opt_primes_file = pcsolver.modes().getPrimesFile().c_str();
	MiniSatPP::opt_convert_weak = false;
	MiniSatPP::opt_convert = MiniSatPP::ct_Sorters;
	pbsolver->allocConstrs(maxvar, sumaggs);

	bool unsat = false;
	for (auto i = pbaggs.begin(); !unsat && i < pbaggs.end(); ++i) {
		unsat = !pbsolver->addConstr((*i)->literals, (*i)->weights, MiniSatPP::Int((*i)->bound), (*i)->sign, false);
	}
	deleteList<PBAgg> (pbaggs);

	if (unsat) {
		delete pbsolver;
		return false;
	}

	//get CNF out of the pseudoboolean matrix
	std::vector<std::vector<MiniSatPP::Lit> > pbencodings;
	unsat = !pbsolver->toCNF(pbencodings);
	delete pbsolver;
	if (unsat) {
		return false;
	}

	//Any literal that is larger than maxvar will have been newly introduced, so should be mapped to nVars()+lit
	//add the CNF to the solver
	int maxnumber = pcsolver.nVars();
	for (auto i = pbencodings.begin(); i < pbencodings.end(); ++i) {
		InnerDisjunction clause;
		for (auto j = (*i).begin(); j < (*i).end(); ++j) {
			Var v = MiniSatPP::var(*j) + (MiniSatPP::var(*j) > maxvar ? maxnumber - maxvar : 0);
			clause.literals.push(mkLit(v, MiniSatPP::sign(*j)));
		}
		pcsolver.add(clause);
	}

	return true;
}

}

#endif /* AGG2SAT_HPP_ */
