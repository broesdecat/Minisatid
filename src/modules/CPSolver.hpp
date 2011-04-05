/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef CPSOLVER_HPP_
#define CPSOLVER_HPP_

#include "modules/DPLLTmodule.hpp"

#include <set>

namespace MinisatID {
namespace CP{

	class CPSolverData;

	/**
	 * Class to interface with cp propagation (and who knows, search engines).
	 *
	 * Interfacing with gecode:
	 * 		include the correct hh files => http://www.gecode.org/doc-latest/reference/PageUsage.html
	 *
	 * 		gecode works as follows:
	 * 			a "Space" object stores the search space, domain, variables, ...
	 * 			constraints, vars and domains can be added to the space
	 * 			space has a "status" operation which propagates until fixpoint or failure
	 */
	class CPSolver: public DPLLTmodule {
	private:
		CPSolverData* 	solverdata; //OWNING pointer

		std::vector<Lit> 	trail;
		std::set<Var>		propagations;

		std::map<Lit, std::vector<Lit>::size_type > propreason;

		int endenqueus;

	public:
				CPSolver	(PCSolver * pcsolver);
		virtual ~CPSolver	();

		bool 	add			(const InnerIntVar& form);
		bool 	add			(const InnerCPBinaryRel& form);
		bool 	add			(const InnerCPBinaryRelVar& form);
		bool 	add			(const InnerCPSum& form);
		bool 	add			(const InnerCPSumWeighted& form);
		bool 	add			(const InnerCPSumWithVar& form);
		bool 	add			(const InnerCPSumWeightedWithVar& form);
		bool 	add			(const InnerCPCount& form);
		bool 	add			(const InnerCPAllDiff& form);

		void 	notifyVarAdded(uint64_t nvars);

		bool 	simplify(){ return true; }

		void 	finishParsing(bool& present, bool& unsat);

		void 	newDecisionLevel		();
		void 	backtrackDecisionLevels(int nblevels, int untillevel);

		rClause propagate	(const Lit& l);
		rClause propagateAtEndOfQueue();

		void 	backtrack	(Lit l);

		rClause getExplanation(const Lit& p);

		void 	printStatistics() const;
		const char* getName() const { return "CP-solver"; }
		void 	print() const;

	private:
		rClause genFullConflictClause();

		rClause notifySATsolverOfPropagation(const Lit& p);
		rClause propagateFinal();

		CPSolverData* getSolverData() const { return solverdata; }
	};

}
}

#endif /* CPSOLVER_HPP_ */
