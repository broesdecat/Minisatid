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
#include "external/MXStatistics.hpp"
#include "utils/Utils.hpp"
#include <memory>

namespace MinisatID {

class PCSolver;
class ModSolver;
class Factory;
struct OptimStatement;

class SearchEngine: public LiteralPrinter {
private:
	std::map<TheoryID, PCSolver*> solvers; // Earlier in list is higher in hierarchy
	std::set<ModSolver*> modsolvers; // Earlier in list is higher in hierarchy
public:
	// NOTE: ownership is passed in
	SearchEngine(PCSolver* solver) {
		solvers[TheoryID(1)]=solver;
	}
	~SearchEngine();
  
  /*****
   * Base interface:
   */
  void addAssumption(const Lit assump);
  void removeAssumption(const Lit assump);
  void clearAssumptions();
  void addAssumptions(const litlist& assumps);
	lbool solve(bool search);

	litlist getUnsatExplanation() const;
	litlist getEntailedLiterals() const;
  
  /*****
   * Old methods:
   */

	TheoryID getBaseTheoryID(){
		return TheoryID(1);
	}

	void createVar(Atom v, TheoryID theoryID);
	Factory& getFactory(TheoryID theoryID);

	Atom newAtom();
	int newSetID();

	int verbosity() const;
	const SolverOption& modes() const;

	lbool rootValue(Lit p) const;
	Lit getTrueLit() const;
	Lit getFalseLit() const;

	void notifyUnsat();
	SATVAL satState() const;
	bool isUnsat() const;

	void setString(const Atom& lit, const std::string& name);
	std::string toString(VarID id) const;
	std::string toString(const Lit& lit) const;
	bool isTseitin(const Atom& atom) const;

	void invalidate(litlist& clause) const;

	void finishParsing();
	bool isOptimizationProblem() const;
	bool hasNextOptimum() const;
	OptimStatement& getNextOptimum();

	void notifyTerminateRequested();

  void getOutOfUnsat();

	std::shared_ptr<Model> getModel();
	lbool getModelValue(Atom v);
	lbool getModelValue(const Lit& lit);
	MXStatistics getStats() const;

	void accept(ConstraintVisitor& visitor);

	bool moreModelsPossible() const;

	// MODAL SUPPORT
	//Get information on hierarchy
	void checkHasSolver(TheoryID level) const;
	bool hasSolver(TheoryID level) const;
	PCSolver* getSolver() const;
	PCSolver* getSolver(TheoryID level) const;
	void add(const SubTheory& subtheory);

	void verifyHierarchy();
	void add(uint level, int constraints);
};

}

#endif /* SEARCHENGINE_HPP_ */
