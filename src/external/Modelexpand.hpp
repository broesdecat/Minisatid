/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#pragma once

#include "Tasks.hpp"

namespace MinisatID {

struct OptimStatement;

// Note: over internal literals, but returns models over output literals
class Modelexpansion {
private:
	Space* space;
	SolverOption modes;

	ModelExpandOptions _options;
	bool setassumptions = false;
	litlist assumptions, currentassumptions; // Note: internal literals, first DECISIONS to make (allows cheap changing of assumptions without complex resets)

	Weight latestintoptimum;
	Lit latestlitoptimum; // For ordered litlist optimization

	bool searchcomplete = false; // if true, no more models exist
	bool optimal = false; //if optimal is true when a model is returned, it is optimal
	bool initial = true;
	bool skipinvalidation = false;
	bool morecpmodelspossible = false;

public:
	Modelexpansion(Space* space, ModelExpandOptions options, const litlist& assumptions);
	~Modelexpansion();

	litlist getUnsatExplanation() const;

	bool isOptimizationProblem() const;
	bool optimumFound() const {
		return optimal;
	}
	bool searchComplete() const {
		return searchcomplete;
	}
	Model* findBetterModel(); // Returns models in the OUTPUT voc!
	Model* findModel(); // Returns models in the OUTPUT voc!

	void notifyTerminateRequested();

	MXStatistics getStats() const;

private:
	bool terminate = false;
	bool terminateRequested() const { return terminate; }
	void setup();

	bool invalidateSuboptimal(OptimStatement& optim, litlist& currentassmpt, bool& setassump, Disjunction& invalidation);
	void invalidateToFindMoreOptimal(OptimStatement& optim);

	void invalidateModel(const litlist& clause);

	litlist savedinvalidation;
	bool invalidateAgg(litlist& invalidation, OptimStatement& optim);
	bool invalidateVar(litlist& invalidation, OptimStatement& optim);
	bool invalidateSubset(litlist& invalidation, litlist& assmpt, OptimStatement& optim);
	bool invalidateValue(litlist& invalidation, OptimStatement& optim);

	Space* getSpace() const {
		return space;
	}
	SearchEngine& getSolver();
	const SolverOption& getOptions() const {
		return modes;
	}
};

Model* getOutputModel(const std::shared_ptr<Model>& remappedmodel, const Remapper& remapper);

}
