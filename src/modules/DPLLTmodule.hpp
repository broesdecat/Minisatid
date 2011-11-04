/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef DPLLTMODULE_HPP_
#define DPLLTMODULE_HPP_

#include "utils/Utils.hpp"
#include "theorysolvers/PCSolver.hpp"

namespace MinisatID {

enum State { PARSING, INITIALIZING, INITIALIZED };

class Propagator {
private:
	State 	init;
	bool	present;
	bool	searchalgo;
	int 	trailindex; //the index in the trail of next propagation to do.
	bool	inqueue;	//used by the queueing mechanism to refrain from putting a propagator in the queue

protected:
	PCSolver* pcsolver;

public:
	Propagator(PCSolver* s) :
			init(PARSING),
			present(true),
			searchalgo(false),
			trailindex(0),
			inqueue(false),
			pcsolver(s) {
		pcsolver->accept(this);
	}
	virtual ~Propagator() {	}

	const PCSolver& getPCSolver() const { return *pcsolver; }
	PCSolver& getPCSolver	() { return *pcsolver; }

	// queueing mech
	void notifyQueued() { inqueue = true; }
	void notifyDeQueued() { inqueue = false; }
	bool isQueued() const { return inqueue; }

	// presence
	bool 	isPresent() const { return present; }
	void	notifyNotPresent() { present = false; }

	// presence
	bool 	isUsedForSearch() const { return searchalgo; }
	void	notifyUsedForSearch() { searchalgo = true; }


	// Propagator methods
	virtual const char* getName			() const = 0;
	virtual int		getNbOfFormulas		() const 					{ return 0; }

	virtual rClause getExplanation		(const Lit&) 				{ assert(false); return nullPtrClause; }
	virtual rClause notifyFullAssignmentFound() 					{ assert(false); return nullPtrClause; }
	virtual void 	finishParsing		(bool& present, bool& unsat){ assert(false); }
		// Checks presence of aggregates and initializes all counters. UNSAT is set to true if unsat is detected
		// PRESENT is set to true if aggregate propagations should be done
	virtual void 	notifyNewDecisionLevel	()						{ assert(false); }
	// NOTE: call explicitly when using hasnextprop/nextprop!
	virtual void 	notifyBacktrack		(int untillevel, const Lit& decision);
	virtual rClause	notifypropagate		()							{ assert(false); return nullPtrClause; }
	virtual Var 	notifyBranchChoice	(const Var& var) const 		{ assert(false); return var; }
	virtual void 	printStatistics		() const 					{ assert(false); }
	virtual void 	printState			() const 					{ assert(false); }
	virtual void 	notifyClauseAdded	(rClause) 					{ assert(false); }
	virtual bool 	symmetryPropagationOnAnalyze(const Lit&) 		{ assert(false); return false; }
	virtual bool 	checkSymmetryAlgo1	(const Lit& lit)			{ assert(false); return false; }
	virtual bool 	checkSymmetryAlgo2	()							{ assert(false); return false; }


	bool 			hasNextProp();
	const Lit&	 	getNextProp();


	// Convenience methods (based on getPCSolver)
	int 	verbosity	() 				const { return getPCSolver().verbosity(); }
	const SolverOption& modes() 		const { return getPCSolver().modes(); }
	bool 	isTrue		(const Lit& l) 	const { return value(l) == l_True; }
	bool 	isTrue		(Var v) 		const { return value(v) == l_True; }
	bool 	isFalse		(const Lit& l) 	const { return value(l) == l_False; }
	bool 	isFalse		(Var v) 		const {	return value(v) == l_False; }
	bool 	isUnknown	(const Lit& l) 	const { return value(l) == l_Undef; }
	bool 	isUnknown	(Var v) 		const { return value(v) == l_Undef; }
	lbool 	value		(Var x) 		const { return getPCSolver().value(x); }
	lbool 	value		(const Lit& p) 	const { return getPCSolver().value(p); }
	int 	nVars		() 				const {	return getPCSolver().nVars(); }

	void	addWatch	(Var atom);
	void	addWatch	(const Lit& lit);

	// State methods
	bool isParsing			() const { return init==PARSING; }
	bool isInitializing 	() const { return init==INITIALIZING; }
	bool isInitialized		() const { return init==INITIALIZED; }
	void notifyParsed		() { assert(isParsing()); init = INITIALIZING; }
	void notifyInitialized	() { /*assert(isInitializing());*/ init = INITIALIZED; } // FIXME add better checking again
};

}

#endif /* DPLLTMODULE_HPP_ */
