//--------------------------------------------------------------------------------------------------
//    Copyright (c) 2009-2010, Broes De Cat, K.U.Leuven, Belgium
//    
//    Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
//    associated documentation files (the "Software"), to deal in the Software without restriction,
//    including without limitation the rights to use, copy, modify, merge, publish, distribute,
//    sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
//    furnished to do so, subject to the following conditions:
//    
//    The above copyright notice and this permission notice shall be included in all copies or
//    substantial portions of the Software.
//    
//    THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
//    NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
//    NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
//    DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
//    OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
//--------------------------------------------------------------------------------------------------

#ifndef DPLLTMODULE_HPP_
#define DPLLTMODULE_HPP_

#include "solvers/utils/Utils.hpp"

namespace MinisatID {

class PCSolver;

class DPLLTmodule {
private:
	bool 			init;

protected:
	PCSolver* 		pcsolver; //NON-OWNING pointer

public:
	DPLLTmodule(PCSolver* s): init(false), pcsolver(s){ }
	virtual ~DPLLTmodule(){};

	bool isInitialized		()	const	{ return init; }
	void notifyInitialized	() 			{ assert(!init); init = true; }

	PCSolver* getPCSolver	()	const 	{ return pcsolver; }

	///////
	// DPLL-T methods
	///////

	virtual void 	notifyVarAdded			(uint64_t nvars) = 0;
	virtual void 	finishParsing		 	(bool& present, bool& unsat) = 0;
	virtual bool 	simplify		() = 0; //False if problem unsat
	virtual rClause propagate				(const Lit& l) = 0;
	virtual rClause propagateAtEndOfQueue	() = 0;
	virtual void 	backtrack				(const Lit& l) = 0;
	virtual void 	newDecisionLevel		() = 0;
	virtual void 	backtrackDecisionLevels	(int nblevels, int untillevel) = 0;

	/*
	 * Returns the explanation for the deduction of p from an aggregate expression.
	 * This method constructs, from the AggReason stored for it, a "reason clause" usable in clause learning.
	 * @post the first element in the reason clause will be the literal itself (invariant by minisat!)
	 * @post the clause is added to the sat solver
	 * @returns NON-OWNING pointer
	 */
	virtual rClause getExplanation			(const Lit& l) = 0;

	virtual void 	printStatistics			() const = 0;

	///////
	// Convenience methods (based on getPCSolver)
	///////

	int 	verbosity	() 				const;

	lbool	value		(Var x) 		const;
	lbool	value		(const Lit& p) const;
	int		nVars		()      		const;

	bool 	isTrue		(const Lit& l) const;
	bool 	isFalse		(const Lit& l) const;
	bool 	isUnknown	(const Lit& l) const;
	bool 	isTrue		(Var l) 		const;
	bool 	isFalse		(Var l) 		const;
	bool 	isUnknown	(Var l) 		const;
};

}

#endif /* DPLLTMODULE_HPP_ */
