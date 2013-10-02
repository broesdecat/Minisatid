/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#include "external/Modelexpand.hpp"

#include "datastructures/OptimStatement.hpp"
#include "space/Remapper.hpp"
#include "external/Translator.hpp"
#include "space/SearchEngine.hpp"
#include "theorysolvers/PropagatorFactory.hpp"
#include "modules/aggsolver/AggProp.hpp"
#include "modules/aggsolver/AggSet.hpp"
#include "modules/IntVar.hpp"
#include "external/Space.hpp"
#include "external/Constraints.hpp"
#include "inferences/Printer.hpp"

using namespace std;
using namespace MinisatID;

Modelexpansion::Modelexpansion(Space* space, ModelExpandOptions options, const litlist& assumptions)
		: 	space(space),
			modes(space->getEngine()->modes()),
			_options(options),
			assumptions(map(assumptions, *space->getRemapper())) {

}

Modelexpansion::~Modelexpansion() {
}

MXStatistics Modelexpansion::getStats() const {
	return getSpace()->getStats();
}

bool Modelexpansion::isOptimizationProblem() const {
	return getSpace()->isOptimizationProblem();
}

litlist Modelexpansion::getUnsatExplanation() const {
	vector<Lit> outmodel;
	for (auto lit : getSpace()->getEngine()->getUnsatExplanation()) {
		if (getSpace()->getRemapper()->wasInput(lit)) {
			outmodel.push_back(getSpace()->getRemapper()->getLiteral(lit));
		}
	}
	return outmodel;
}

void Modelexpansion::notifyTerminateRequested() {
	terminate = true;
	space->getEngine()->notifyTerminateRequested();
}

// If NULL is returned, no model was found or search was aborted
void Modelexpansion::setup() {
	getSpace()->getEngine()->finishParsing();
	if (getSpace()->isCertainlyUnsat()) {
		searchcomplete = true;
	}

	if (getSpace()->isOptimizationProblem() && getSpace()->isAlwaysAtOptimum()) {
		optimal = true;
	}

	currentassumptions = assumptions;
	setassumptions = true;
}

// TODO not for multiple optimization statements yet
Model* Modelexpansion::findBetterModel() {
	MAssert(getSolver().isOptimizationProblem());
	if (optimal) {
		return NULL;
	}
	bool unsatreached = false;
	if (initial) {
		setup();
		if (searchcomplete) {
			initial = false;
			return NULL;
		}
	} else {
		Disjunction invalidation(DEFAULTCONSTRID, { });
		unsatreached = invalidateSuboptimal(getSolver().getCurrentOptimum(), currentassumptions, setassumptions, invalidation);
		if(not unsatreached){
			invalidateModel(invalidation.literals);
		}
		unsatreached |= not getSolver().moreModelsPossible();
	}

	shared_ptr<Model> model = NULL;
	if (not unsatreached) {
		if (setassumptions) {
			getSolver().setAssumptions(currentassumptions);
			setassumptions = false;
		}
		auto state = getSolver().solve(true);
		savedinvalidation = getSolver().getInvalidation();
		model = getSpace()->getEngine()->getModel();
		if (state == l_Undef || terminateRequested()) {
			return NULL;
		}
		unsatreached = state == l_False;
		if(not unsatreached){
			getSolver().saveState();
		}
	}
	if (unsatreached) {
		if (not initial) {
			optimal = true;
			getSolver().resetState();
			getSolver().setAssumptions(assumptions); // Note: prevents when finding multiple models, that in findnext, reset is called again (as assmpts have just been set)
			// TODO In fact from here the state no longer has to be saved
			invalidateToFindMoreOptimal(getSolver().getCurrentOptimum());
			// store whether there might be more cp models possible before really invalidating the clause
			morecpmodelspossible = getSolver().hasCPSolver();
			skipinvalidation = true;
		}
		initial = false;
		if(getSolver().satState()==SATVAL::UNSAT){
			searchcomplete = true;
		}
		return NULL;
	}

	initial = false;

	return getOutputModel(model, *getSpace()->getRemapper());
}

Model* Modelexpansion::findModel() {
	if (getSolver().isOptimizationProblem()) {
		MAssert(optimal);
	}
	if (searchcomplete) {
		return NULL;
	}
	if (initial) {
		setup();
		initial = false;
	} else if(not skipinvalidation) {
		if (morecpmodelspossible) {
			//Check for more models with different var assignment
			if (getSolver().findNextCPModel() == SATVAL::UNSAT) {
				morecpmodelspossible = false;
			} else {
				return getOutputModel(getSpace()->getEngine()->getModel(), *getSpace()->getRemapper());
			}
		}
		if (getSolver().moreModelsPossible()) {
			Disjunction invalidation(DEFAULTCONSTRID, savedinvalidation);
			invalidateModel(invalidation.literals);
			searchcomplete = getSolver().satState() == SATVAL::UNSAT;
		} else {
			searchcomplete = true;
		}
	}
	skipinvalidation = false;
	if (searchcomplete) {
		return NULL;
	}

	if (setassumptions) {
		getSolver().setAssumptions(currentassumptions);
		setassumptions = false;
	}
	auto state = getSolver().solve(true);
	savedinvalidation = getSolver().getInvalidation();
	if (state == l_Undef || terminateRequested()) {
		return NULL;
	}
	if (state == l_False || searchcomplete) {
		searchcomplete = true;
		return NULL;
	}

	// store whether there might be more cp models possible before really invalidating the clause
	morecpmodelspossible = getSolver().hasCPSolver();
	return getOutputModel(getSpace()->getEngine()->getModel(), *getSpace()->getRemapper());
}

bool Modelexpansion::invalidateSuboptimal(OptimStatement& optim, litlist& currentassmpt, bool& setassump, Disjunction& invalidation) {
	auto unsatreached = false;
	//invalidate the solver
	switch (optim.optim) {
	case Optim::LIST:
		unsatreached = invalidateValue(invalidation.literals, optim);
		break;
	case Optim::SUBSET:
		currentassmpt.clear();
		setassump = true;
		unsatreached = invalidateSubset(invalidation.literals, currentassmpt, optim);
		break;
	case Optim::AGG:
		unsatreached = invalidateAgg(invalidation.literals, optim);
		break;
	case Optim::VAR: {
		unsatreached = invalidateVar(invalidation.literals, optim);
		break;
	}
	}
	return unsatreached;
}

void Modelexpansion::invalidateToFindMoreOptimal(OptimStatement& optim) {
	// Prevent to find the first model again
	internalAdd(Disjunction(DEFAULTCONSTRID, savedinvalidation), getSolver().getBaseTheoryID(), getSolver());

	// If resetting state, also fix the optimization constraints to their optimal condition
	switch (optim.optim) {
	case Optim::LIST:
		for (auto i = optim.to_minimize.cbegin(); i < optim.to_minimize.cend(); ++i) {
			if (*i == latestlitoptimum) {
				break;
			}
			internalAdd(Disjunction(DEFAULTCONSTRID, { ~*i }), getSolver().getBaseTheoryID(), getSolver());
		}
		internalAdd(Disjunction(DEFAULTCONSTRID, { latestlitoptimum }), getSolver().getBaseTheoryID(), getSolver());
		break;
	case Optim::SUBSET: {
		WLSet set(getSolver().newSetID());
		for (auto i = optim.to_minimize.cbegin(); i < optim.to_minimize.cend(); ++i) {
			set.wl.push_back( { *i, 1 });
		}
		internalAdd(set, getSolver().getBaseTheoryID(), getSolver());
		auto var = getSolver().newAtom();
		internalAdd(Disjunction(DEFAULTCONSTRID, { mkPosLit(var) }), getSolver().getBaseTheoryID(), getSolver());
		internalAdd(Aggregate(DEFAULTCONSTRID, mkPosLit(var), set.setID, latestintoptimum, AggType::CARD, AggSign::UB, AggSem::COMP, -1, false), getSolver().getBaseTheoryID(), getSolver());
		break;
	}
	case Optim::AGG: {
		auto agg = optim.agg_to_minimize;
		agg->setBound(AggBound(agg->getSign(), latestintoptimum));
		agg->reInitializeAgg();
		break;
	}
	case Optim::VAR: {
		internalAdd(Disjunction(DEFAULTCONSTRID, { optim.var->getEQLit(latestintoptimum) }), getSolver().getBaseTheoryID(), getSolver());
		break;
	}
	}
}

void Modelexpansion::invalidateModel(const litlist& clause) {
	Disjunction d(DEFAULTCONSTRID, clause);
	if (getOptions().verbosity >= 3) {
		clog << "Adding model-invalidating clause: [ ";
		clog << getSpace()->toString(d.literals);
		clog << "]\n";
	}
	internalAdd(d, getSolver().getBaseTheoryID(), getSolver());
}

// Invalidation returns true if optimum has certainly been found

bool Modelexpansion::invalidateSubset(litlist& invalidation, litlist& assmpt, OptimStatement& optim) {
	int subsetsize = 0;
	const auto& minim = optim.to_minimize;
	for (auto i = minim.cbegin(); i < minim.cend(); ++i) {
		auto lit = *i;
		if (getSolver().getModelValue(var(lit)) == l_True) {
			invalidation.push_back(~lit);
			++subsetsize;
		} else {
			assmpt.push_back(~lit);
		}
	}

	latestintoptimum = subsetsize;

	if (subsetsize == 0) {
		return true; //optimum has already been found!!!
	} else {
		return false;
	}
}

bool Modelexpansion::invalidateValue(litlist& invalidation, OptimStatement& optim) {
	bool currentoptimumfound = false;

	const auto& minim = optim.to_minimize;
	for (uint i = 0; !currentoptimumfound && i < minim.size(); ++i) {
		if (!currentoptimumfound && getSolver().getModelValue(var(minim[i])) == l_True) {
			if (getOptions().verbosity >= 1) {
				clog << "> Current optimum found for: ";
				clog << getSpace()->toString(minim[i]);
				clog << "\n";
			}
			currentoptimumfound = true;
			latestlitoptimum = minim[i];
		}
		if (!currentoptimumfound) {
			invalidation.push_back(minim[i]);
		}
	}

	if (invalidation.size() == 0) {
		return true; //optimum has already been found!!!
	} else {
		return false;
	}
}

bool Modelexpansion::invalidateAgg(litlist& invalidation, OptimStatement& optim) {
	auto agg = optim.agg_to_minimize;
	auto s = agg->getSet();
	latestintoptimum = s->getType().getValue(*s);

	if (getOptions().verbosity >= 1) {
		clog << "> Current optimal value " << latestintoptimum << "\n";
	}

	agg->setBound(AggBound(agg->getSign(), latestintoptimum - 1));

	if (s->getType().getMinPossible(*s) == latestintoptimum) {
		return true;
	}

	HeadReason ar(*agg, mkNegLit(var(agg->getHead())));
	s->getProp()->getExplanation(invalidation, ar);

	return false;
}

bool Modelexpansion::invalidateVar(litlist& invalidation, OptimStatement& optim) {
	auto var = optim.var;
	latestintoptimum = var->maxValue();
	if (getOptions().verbosity >= 1) {
		clog << "> Current optimal value " << latestintoptimum << "\n";
	}

	if (var->origMinValue() == latestintoptimum) {
		return true;
	}

	invalidation.push_back(var->getLEQLit(latestintoptimum - 1));
	return false;
}

SearchEngine& Modelexpansion::getSolver() {
	return *getSpace()->getEngine();
}

//Translate into original vocabulary
Model* MinisatID::getOutputModel(const std::shared_ptr<Model>& model, const Remapper& remapper) {
	auto outmodel = new Model();

	for (auto lit : model->literalinterpretations) {
		if (remapper.wasInput(lit)) {
			outmodel->literalinterpretations.push_back(remapper.getLiteral(lit));
		}
	}
	sort(outmodel->literalinterpretations.begin(), outmodel->literalinterpretations.end());

	for (auto vareq : model->variableassignments) {
		if (remapper.wasInput(vareq.variable)) {
			outmodel->variableassignments.push_back( { remapper.getOrigID(vareq.variable), vareq.value });
		}
	}

	return outmodel;
}
