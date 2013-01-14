/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#include "external/Tasks.hpp"

#include "space/Remapper.hpp"
#include "external/Translator.hpp"
#include "space/SearchEngine.hpp"
#include "theorysolvers/PropagatorFactory.hpp"
#include "modules/aggsolver/AggProp.hpp"
#include "modules/aggsolver/AggSet.hpp"
#include "modules/IntVar.hpp"
#include "external/SearchMonitor.hpp"
#include "external/FlatZincRewriter.hpp"
#include "external/ECNFPrinter.hpp"
#include "constraintvisitors/CNFPrinter.hpp"
#include "constraintvisitors/ECNFGraphPrinter.hpp"
#include "constraintvisitors/HumanReadableParsingPrinter.hpp"
#include "Printer.hpp"
#include "ModelManager.hpp"
#include "external/utils/ResourceManager.hpp"
#include "external/Space.hpp"
#include "external/Constraints.hpp"

#include <map>
#include <vector>

using namespace std;
using namespace MinisatID;

VarID VarCreation::createID(){
	return {remapper->getNewID()};
}

Atom VarCreation::createVar() {
	return remapper->getNewVar();
}

void Task::execute() {
	innerExecute();
}
void SpaceTask::execute() {
	space->getEngine()->finishParsing();
	space->notifyInferenceExecuted();
	Task::execute();
}
void Task::notifyTerminateRequested() {
	terminate = true;
}
void SpaceTask::notifyTerminateRequested() {
	Task::notifyTerminateRequested();
	space->getEngine()->notifyTerminateRequested();
}

// NOTE: EXTERNAL literals
ModelExpand::ModelExpand(Space* space, ModelExpandOptions options, const litlist& assumptions)
		: MXTask(space), _options(options), assumptions(map(assumptions, *space->getRemapper())), _solutions(new ModelManager(options.savemodels)),
			printer(new Printer(_solutions, space, options.printmodels, space->getOptions())) {

}

ModelExpand::~ModelExpand() {
	delete (_solutions);
	delete (printer);
}

int ModelExpand::getNbModelsFound() const {
	if (getSpace()->isOptimizationProblem() && not _solutions->hasOptimalModel()) {
		return 0;
	}
	return _solutions->getNbModelsFound();
}

SearchEngine& SpaceTask::getSolver() const {
	return *getSpace()->getEngine();
}

SpaceTask::SpaceTask(Space* space)
		: Task(space->getOptions()), space(space) {

}

const modellist& ModelExpand::getSolutions() const {
	return _solutions->getModels();
}
modellist ModelExpand::getBestSolutionsFound() const {
	if(not getSpace()->isOptimizationProblem()){
		throw idpexception("Cannot return best models when not doing optimization inference.");
	}
	return _solutions->getBestModelsFound();
}

Weight ModelExpand::getBestValueFound() const{
	if(not getSpace()->isOptimizationProblem()){
		throw idpexception("Cannot return best models when not doing optimization inference.");
	}
	return _solutions->getBestValueFound();
}

bool ModelExpand::isSat() const {
	return _solutions->isSat();
}
bool ModelExpand::isUnsat() const {
	return _solutions->isUnsat();
}

litlist ModelExpand::getUnsatExplanation() const {
	return getSolver().getUnsatExplanation();
}

void ModelExpand::notifySolvingAborted() {
	printer->notifySolvingAborted();
}

/*
 * Possible answers:
 * true => satisfiable, at least one model exists (INDEPENDENT of the number of models requested or found)
 * false => unsatisfiable
 *
 * Possible tasks:
 * do propagation => do not do search, do not save any model
 * check satisfiability => save the first model
 * find n/all models and print them => do not save models, but print them one at a time
 * find n/all models and return them => save all models
 * count the number of models => do not save models
 */
void ModelExpand::innerExecute() {
	printer->notifyStartSolving();
	if (getSpace()->isCertainlyUnsat()) {
		_solutions->notifyUnsat();
		printer->notifySolvingFinished();
		return;
	}

	if (getSpace()->isOptimizationProblem()) {
		printer->notifyOptimizing();
	}

	printSearchStart(clog, getOptions().verbosity);

	bool moremodelspossible = true;
	if (getSpace()->isOptimizationProblem()) {
		bool optimumfound = true;
		if (getSpace()->isAlwaysAtOptimum()) {
			findNext(assumptions, _options);
			optimumfound = _solutions->getNbModelsFound() > 0;
		} else {
			while (getSolver().hasNextOptimum() && optimumfound) {
				optimumfound = findOptimal(assumptions, getSolver().getNextOptimum());
			}
		}

		if (optimumfound) {
			_solutions->notifyOptimalModelFound();
		} else {
			moremodelspossible = false;
		}
	}
	if (moremodelspossible) {
		auto moremodels = findNext(assumptions, _options);
		if (moremodels == MXState::UNSAT) {
			if (getNbModelsFound() == 0) {
				printNoModels(clog, getOptions().verbosity);
			} else {
				printer->notifyNoMoreModels();
				printNoMoreModels(clog, getOptions().verbosity);
			}
		}
	}
	if (_solutions->getNbModelsFound() == 0) {
		_solutions->notifyUnsat();
		getSpace()->notifyUnsat();
	}
	if (terminateRequested()) {
		printer->notifySolvingAborted();
	} else {
		printer->notifySolvingFinished();
	}
}

//Translate into original vocabulary
vector<Lit> getBackMappedModel(const std::vector<Lit>& model, const Remapper& r) {
	vector<Lit> outmodel;
	for (auto lit : model) {
		if (r.wasInput(lit)) {
			outmodel.push_back(r.getLiteral(lit));
		}
	}
	sort(outmodel.begin(), outmodel.end());
	return outmodel;
}
vector<VariableEqValue> getBackMappedModel(const std::vector<VariableEqValue>& model, const Remapper& r) {
	vector<VariableEqValue> outmodel;
	for (auto vareq : model) {
		if (r.wasInput(vareq.variable)) {
			outmodel.push_back({r.getOrigID(vareq.variable),vareq.value});
		}
	}
	return outmodel;
}
void addModelToSolution(const std::shared_ptr<Model>& model, const Remapper& remapper, ModelManager& solution, Printer& printer) {
	auto outmodel = new Model();
	outmodel->literalinterpretations = getBackMappedModel(model->literalinterpretations, remapper);
	outmodel->variableassignments = getBackMappedModel(model->variableassignments, remapper);
	solution.addModel(outmodel);
	printer.addModel(outmodel);

}

void ModelExpand::addModel(std::shared_ptr<Model> model) {
	addModelToSolution(model, *getSpace()->getRemapper(), *_solutions, *printer);
}

bool findmoreModels(const ModelExpandOptions& options, ModelManager* m) {
	return options.nbmodelstofind == 0 || m->getNbModelsFound() < options.nbmodelstofind;
}

/**
 * Checks satisfiability of the theory.
 * Returns false if no model was found, true otherwise.
 * If a model is found, it is printed and returned in <m>, the theory is extended to prevent
 * 		the same model from being found again and
 * 		the datastructures are reset to prepare to find the next model
 */
/**
 * Important: assmpt are the first DECISIONS that are made. So they are not automatic unit propagations
 * and can be backtracked!
 */
MXState ModelExpand::findNext(const litlist& assmpt, const ModelExpandOptions& options) {
	bool moremodels = true; // True if more models might exist
	getSolver().setAssumptions(assmpt);
	while (moremodels && findmoreModels(options, _solutions)) {
		auto state = getSolver().solve(true);
		if (state == l_Undef || terminateRequested()) {
			return MXState::UNKNOWN;
		}
		bool modelfound = state == l_True;

		if (not modelfound) {
			moremodels = false;
			break;
		}

		addModel(getSpace()->getEngine()->getModel());

		// => first check whether there might be more CP models before backtracking completely!
		// Probably better refactor to put this deeper?
		bool morecpmodels = getSolver().hasCPSolver();
		if (morecpmodels) {
			//Check for more models with different var assignment
			while (morecpmodels && findmoreModels(options, _solutions)) {
				if (getSolver().findNextCPModel() == SATVAL::UNSAT) {
					morecpmodels = false;
				} else {
					addModel(getSpace()->getEngine()->getModel());
				}
			}
		}

		if (not findmoreModels(options, _solutions)) { // Do not invalidate if enough models have been found
			break;
		}

		//Invalidate SAT model
		if (getSolver().moreModelsPossible()) { //choices were made, so other models possible
			Disjunction invalidation(DEFAULTCONSTRID, {});
			getSolver().invalidate(invalidation.literals);
			moremodels = invalidateModel(invalidation.literals) == SATVAL::POS_SAT;
		} else {
			if (not morecpmodels) {
				moremodels = false;
			}
		}

	}

	return moremodels ? MXState::MODEL : MXState::UNSAT;
}

/**
 * Returns false if invalidating the model leads to UNSAT, meaning that no more models are possible. Otherwise true.
 */
SATVAL ModelExpand::invalidateModel(const litlist& clause) {
	Disjunction d(DEFAULTCONSTRID, clause);

	if (getOptions().verbosity >= 3) {
		clog << "Adding model-invalidating clause: [ ";
		clog << getSpace()->toString(d.literals);
		clog << "]\n";
	}
	internalAdd(d, getSolver().getBaseTheoryID(), getSolver());
	return getSolver().satState();
}

// OPTIMIZATION METHODS
bool ModelExpand::invalidateSubset(litlist& invalidation, litlist& assmpt, OptimStatement& optim) {
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

	_solutions->setLatestOptimum(subsetsize);

	if (subsetsize == 0) {
		return true; //optimum has already been found!!!
	} else {
		return false;
	}
}

bool ModelExpand::invalidateValue(litlist& invalidation, OptimStatement& optim) {
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
			_solutions->setLatestOptimum(minim[i]);
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

bool ModelExpand::invalidateAgg(litlist& invalidation, OptimStatement& optim) {
	auto agg = optim.agg_to_minimize;
	auto s = agg->getSet();
	auto bestvalue = s->getType().getValue(*s);
	_solutions->setLatestOptimum(bestvalue);
	printer->notifyCurrentOptimum(bestvalue);

	if (getOptions().verbosity >= 1) {
		clog << "> Current optimal value " << bestvalue << "\n";
	}

	agg->setBound(AggBound(agg->getSign(), bestvalue - 1));

	if (s->getType().getMinPossible(*s) == bestvalue) {
		return true;
	}

	HeadReason ar(*agg, mkNegLit(var(agg->getHead())));
	s->getProp()->getExplanation(invalidation, ar);

	return false;
}

bool ModelExpand::invalidateVar(litlist& invalidation, OptimStatement& optim) {
	auto var = optim.var;
	auto bestvalue = var->maxValue();
	_solutions->setLatestOptimum(bestvalue);
	printer->notifyCurrentOptimum(bestvalue);
	if (getOptions().verbosity >= 1) {
		clog << "> Current optimal value " << bestvalue << "\n";
	}

	if (var->origMinValue() == bestvalue) {
		return true;
	}

	invalidation.push_back(var->getLEQLit(bestvalue - 1));
	return false;
}

/*
 * If the optimum possible value is reached, the model is not invalidated. Otherwise, unsat has to be found first, so it is invalidated.
 *
 * If the optimal model was found, the state is reset such that more models might be found with that same value.
 *
 * Returns true if an optimal model was found
 */
bool ModelExpand::findOptimal(const litlist& assmpt, OptimStatement& optim) {
	litlist currentassmpt = assmpt;
	bool setassump = true;

	bool modelfound = false, unsatreached = false;

	while (not unsatreached) {
		if (optim.optim == Optim::AGG) {
			// NOTE: necessary to propagate the changes to the bound correctly
			if (optim.agg_to_minimize->reInitializeAgg() == SATVAL::UNSAT) {
				unsatreached = true;
				continue;
			}
		}

		if (setassump) {
			getSolver().setAssumptions(currentassmpt); // NOTE do not do this if the assumptions have not changed!
			setassump = false;
		}

		auto sat = getSolver().solve(true);
		if (sat == l_False) {
			unsatreached = true;
			break;
		} else if (sat == l_Undef) {
			break;
		}
		modelfound = true;
		savedinvalidation.clear();
		getSolver().invalidate(savedinvalidation);

		//Store current model in m before invalidating the solver
		auto m = getSolver().getModel();

		getSolver().saveState();

		//invalidate the solver
		Disjunction invalidation(DEFAULTCONSTRID, {});
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

		if (not unsatreached) {
			if (getSolver().moreModelsPossible()) { //choices were made, so other models possible
				unsatreached = invalidateModel(invalidation.literals) == SATVAL::UNSAT;
			} else {
				unsatreached = true;
			}
		}

		addModel(m);
	}

	//cerr <<"Unsat found, enabling finding more models\n";
	if (unsatreached && modelfound) {
		getSolver().resetState();
		getSolver().setAssumptions(assmpt); // Note: prevents when finding multiple models, that in findnext, reset is called again (as assmpts have just been set)

		// TODO In fact from here the state no longer has to be saved

		// Prevent to find the first model again
		internalAdd(Disjunction(DEFAULTCONSTRID, savedinvalidation), getSolver().getBaseTheoryID(), getSolver());

		// If resetting state, also fix the optimization constraints to their optimal condition
		switch (optim.optim) {
		case Optim::LIST:
			for (auto i = optim.to_minimize.cbegin(); i < optim.to_minimize.cend(); ++i) {
				if (*i == _solutions->getBestLitFound()) {
					break;
				}
				internalAdd(Disjunction(DEFAULTCONSTRID, { ~*i }), getSolver().getBaseTheoryID(), getSolver());
			}
			internalAdd(Disjunction(DEFAULTCONSTRID, { _solutions->getBestLitFound() }), getSolver().getBaseTheoryID(), getSolver());
			break;
		case Optim::SUBSET: {
			WLSet set(getSolver().newSetID());
			for (auto i = optim.to_minimize.cbegin(); i < optim.to_minimize.cend(); ++i) {
				set.wl.push_back( { *i, 1 });
			}
			internalAdd(set, getSolver().getBaseTheoryID(), getSolver());
			auto var = getSolver().newVar();
			internalAdd(Disjunction(DEFAULTCONSTRID, { mkPosLit(var) }), getSolver().getBaseTheoryID(), getSolver());
			internalAdd(Aggregate(DEFAULTCONSTRID, mkPosLit(var), set.setID, _solutions->getBestValueFound(), AggType::CARD, AggSign::UB, AggSem::COMP, -1, false), getSolver().getBaseTheoryID(), getSolver());
			break;
		}
		case Optim::AGG: {
			auto agg = optim.agg_to_minimize;
			agg->setBound(AggBound(agg->getSign(), _solutions->getBestValueFound()));
			agg->reInitializeAgg();
			break;
		}
		case Optim::VAR: {
			internalAdd(Disjunction(DEFAULTCONSTRID, { optim.var->getEQLit(_solutions->getBestValueFound()) }), getSolver().getBaseTheoryID(), getSolver());
			break;
		}
		}
	}

	return unsatreached && modelfound;
}

void Monitor::notifyMonitor(const Lit& propagation, int decisionlevel) {
	for (auto i = monitors.cbegin(); i < monitors.cend(); ++i) {
		if (remapper->wasInput(propagation)) {
			(*i)->notifyPropagated(remapper->getLiteral(propagation), decisionlevel);
		}
	}
}

void Monitor::notifyMonitor(int untillevel) {
	for (auto i = monitors.cbegin(); i < monitors.cend(); ++i) {
		(*i)->notifyBacktracked(untillevel);
	}
}

void ModelExpand::notifyCurrentOptimum(const Weight& value) const {
	printer->notifyCurrentOptimum(value);
}

literallist UnitPropagate::getEntailedLiterals() const {
	auto lits = getSolver().getEntailedLiterals();
	literallist literals;
	auto r = *getSpace()->getRemapper();
	for (auto i = lits.cbegin(); i < lits.cend(); ++i) {
		if (getSolver().rootValue(*i) != l_Undef && r.wasInput(*i)) {
			literals.push_back(r.getLiteral(*i));
		}
	}
	return literals;
}

void UnitPropagate::innerExecute() {
	getSolver().setAssumptions(assumptions);
	getSolver().solve(false);
}

void UnitPropagate::writeOutEntailedLiterals() {
	auto resman = createResMan(getOptions().outputfile);
	ostream output(resman->getBuffer());

	clog << ">>> Following is a list of literals entailed by the theory.\n";
	const auto& lits = getEntailedLiterals();
	bool begin = true;
	for (auto i = lits.cbegin(); i < lits.cend(); ++i) {
		if (not begin) {
			output << " ";
		}
		begin = false;
		output << getSpace()->toString(*i);
	}
	output << "\n";
	resman->close();
}

void Transform::innerExecute() {
	std::shared_ptr<ResMan> resfile(createResMan(getSpace()->getOptions().outputfile));
	ostream output(resfile->getBuffer());
	switch (outputlanguage) {
	case TheoryPrinting::FZ: {
		FlatZincRewriter<ostream> fzrw(getSpace()->getRemapper(), getSpace()->getTranslator(), getOptions(), output);
		getSolver().accept(fzrw);
		break;
	}
	case TheoryPrinting::ECNF: {
		RealECNFPrinter<ostream> pr(getSpace()->getEngine(), output);
		getSolver().accept(pr);
		break;
	}
	case TheoryPrinting::CNF: {
		RealCNFPrinter<ostream> pr(getSpace()->getEngine(), output);
		getSolver().accept(pr);
		break;
	}
	case TheoryPrinting::ECNFGRAPH: {
		ECNFGraphPrinter<ostream> pr(getSpace()->getEngine(), output);
		getSolver().accept(pr);
		break;
	}
	case TheoryPrinting::HUMAN: {
		HumanReadableParsingPrinter<ostream> pr(getSpace()->getEngine(), output);
		getSolver().accept(pr);
		break;
	}
	}
}
