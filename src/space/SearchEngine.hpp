/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef SEARCHENGINE_HPP_
#define SEARCHENGINE_HPP_

#include "external/LiteralPrinter.hpp"
#include "utils/Utils.hpp"
#include <memory>

namespace MinisatID{

class PCSolver;
class PropagatorFactory;
struct OptimStatement;

class SearchEngine: public LiteralPrinter {
private:
	PCSolver* solver;
public:
	// NOTE: ownership is passed in
	SearchEngine(PCSolver* solver): solver(solver){}
	~SearchEngine();
	PropagatorFactory& getFactory();
	void createVar(Atom v);
	int verbosity() const;
	const SolverOption& modes() const;
	Atom newVar();
	int newSetID();
	lbool rootValue(Lit p) const;
	Lit getTrueLit() const;
	Lit getFalseLit() const;

	void notifyUnsat();
	SATVAL satState() const;
	bool isUnsat() const;

	std::string toString(VarID id) const;
	std::string toString(const Lit& lit) const;

	void invalidate(litlist& clause) const;

	void finishParsing();
	bool isOptimizationProblem() const;
	bool isAlwaysAtOptimum() const;
	bool hasNextOptimum() const;
	OptimStatement& getNextOptimum();

	bool hasCPSolver() const;
	SATVAL findNextCPModel();

	void notifyTerminateRequested();

	void saveState();
	void resetState();

	std::shared_ptr<Model> getModel();
	lbool getModelValue(Atom v);
	lbool getModelValue(const Lit& lit);

	void accept(ConstraintVisitor& visitor);

	void setAssumptions(const litlist& assumps);
	lbool solve(bool search);
	litlist getUnsatExplanation() const;

	litlist getEntailedLiterals() const;
	bool moreModelsPossible() const;
};

}

#endif /* SEARCHENGINE_HPP_ */
