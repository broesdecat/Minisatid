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
#include <bitset>

using namespace std;
using namespace MinisatID;


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

VarID VarCreation::createID(){
	return {remapper->getNewID()};
}

Atom VarCreation::createVar() {
	return remapper->getNewVar();
}

/*
 * Task
 */
void Task::execute() {
	innerExecute();
}
void Task::notifyTerminateRequested() {
	terminate = true;
}

/*
 * SpaceTask
 */
SpaceTask::SpaceTask(Space* space)
		: Task(space->getOptions()), space(space) {

}
SearchEngine& SpaceTask::getSolver() const {
	return *getSpace()->getEngine();
}
void SpaceTask::execute() {
	space->getEngine()->finishParsing();
	space->notifyInferenceExecuted();
	Task::execute();
}
void SpaceTask::notifyTerminateRequested() {
	Task::notifyTerminateRequested();
	space->getEngine()->notifyTerminateRequested();
}

/**
 * FindModels
 */

FindModels::FindModels(Space* space, ModelExpandOptions opts, const litlist& assumptions)
  : ModelExpand(space,opts,assumptions), nbModels(opts.nbmodelstofind){
  
}

FindModels::~FindModels(){
}

void FindModels::innerExecute(){
  printer->notifyStartSolving();
	if (getSpace()->isCertainlyUnsat()) {
		printer->notifySolvingFinished();
		return;
	}
  
	printSearchStart(clog, getOptions().verbosity);
  getSolver().setAssumptions(assumptions);
  
  auto state = getSolver().solve(true);
  if (state == l_Undef || terminateRequested()) {
    printer->notifySolvingAborted();
    return;
  }else if(state==l_False){
    getSpace()->notifyUnsat();
    return;
  }else{ // model found :)
    addModel(getSpace()->getEngine()->getModel());
  }
  
  while(nbModels==0 || nbModels > _solutions->getNbModelsFound()){
    invalidateModel();
    state = getSolver().solve(true);
  
    if (state == l_Undef || terminateRequested()) {
      printer->notifySolvingAborted();
      return;
    }else if(state==l_False){
      break;
    }
    
    addModel(getSpace()->getEngine()->getModel());
  }
  printer->notifySolvingFinished();
}

/*
 * ModelExpand
 */
// NOTE: EXTERNAL literals
ModelExpand::ModelExpand(Space* space, ModelExpandOptions options, const litlist& assumptions)
		: SpaceTask(space), _options(options), assumptions(map(assumptions, *space->getRemapper())), _solutions(new ModelManager(options.savemodels)),
			printer(new Printer(_solutions, space, options.printmodels, space->getOptions())) {
}

ModelExpand::~ModelExpand() {
	delete (_solutions);
	delete (printer);
}

MXStatistics ModelExpand::getStats() const{
	return getSpace()->getStats();
}

int ModelExpand::getNbModelsFound() const {
	if (getSpace()->isOptimizationProblem() && not _solutions->hasOptimalModel()) {
		return 0;
	}
	return _solutions->getNbModelsFound();
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
	vector<Lit> outmodel;
	for (auto lit : getSolver().getUnsatExplanation()) {
		if (getSpace()->getRemapper()->wasInput(lit)) {
			outmodel.push_back(getSpace()->getRemapper()->getLiteral(lit));
		}
	}
	return outmodel;
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
    while (getSolver().hasNextOptimum() && optimumfound) {
      optimumfound = findOptimal(assumptions, getSolver().getNextOptimum());
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
	if (isUnsat()) {
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
		if (r.wasInput(vareq.getVariable())) {
			auto image = vareq.hasValue();
			outmodel.push_back({r.getOrigID(vareq.getVariable()), image?vareq.getValue() : 0, image});
		}
	}
	return outmodel;
}

void ModelExpand::addModel(std::shared_ptr<Model> model) {
  auto outmodel = new Model();
	outmodel->literalinterpretations = getBackMappedModel(model->literalinterpretations, *getSpace()->getRemapper());
	outmodel->variableassignments = getBackMappedModel(model->variableassignments, *getSpace()->getRemapper());
	_solutions->addModel(outmodel);
	printer->addModel(outmodel);
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
	getSolver().setAssumptions(assmpt);
	auto state = MXState::MODEL;
	while (state == MXState::MODEL && findmoreModels(options, _solutions)) {
		state = findNext();
	}
	return state;
}

MXState ModelExpand::findNext() {
	auto state = getSolver().solve(true);
	if (state == l_Undef || terminateRequested()) {
		return MXState::UNKNOWN;
	}
	bool modelfound = state == l_True;
	if (not modelfound) {
		return MXState::UNSAT;
	}

	addModel(getSpace()->getEngine()->getModel());
	//Invalidate SAT model
	if (!getSolver().moreModelsPossible()) {
		return MXState::MODEL_FINAL;
	}
	//choices were made, so other models possible
	auto invalidatedState = invalidateModel();
	if(invalidatedState != SATVAL::POS_SAT){
		return MXState::MODEL_FINAL;
	}
	return MXState::MODEL;
}

SATVAL ModelExpand::invalidateModel() {
	Disjunction invalidation({});
	getSolver().invalidate(invalidation.literals);
	return invalidateModel(invalidation);
}

/**
 * Returns false if invalidating the model leads to UNSAT, meaning that no more models are possible. Otherwise true.
 */
SATVAL ModelExpand::invalidateModel(Disjunction& clause) {
	if (getOptions().verbosity >= 3) {
		clog << "Adding model-invalidating clause: [ ";
		clog << getSpace()->toString(clause.literals);
		clog << "]\n";
	}
	internalAdd(clause, getSolver().getBaseTheoryID(), getSolver());
	return getSolver().satState();
}

// OPTIMIZATION METHODS
bool ModelExpand::invalidateSubset(litlist& invalidation, OptimStatement& optim) {
	int subsetsize = 0;
	const auto& minim = optim.to_minimize;
	for (auto i = minim.cbegin(); i < minim.cend(); ++i) {
		auto lit = *i;
		if (getSolver().getModelValue(var(lit)) == l_True) {
			invalidation.push_back(~lit);
			++subsetsize;
		} else {
      // add unit clauses to ensure subsetminimality
      // TODO: duplicate unit clauses which now will be deleted by simplification. This can be more efficient.
      internalAdd(Disjunction({~lit}), getSolver().getBaseTheoryID(), getSolver());
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

	if(optim.minimize){
		if (var->origMinValue() == bestvalue) {
			return true;
		}
		invalidation.push_back(var->getLEQLit(bestvalue - 1));
	}else{
		if (var->origMaxValue() == bestvalue) {
			return true;
		}
		invalidation.push_back(var->getGEQLit(bestvalue + 1));
	}
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

	bool modelfound = false, unsatreached = false;

	while (not unsatreached) {
		if (optim.optim == Optim::AGG) {
			// NOTE: necessary to propagate the changes to the bound correctly
			if (optim.agg_to_minimize->reInitializeAgg() == SATVAL::UNSAT) {
				unsatreached = true;
				continue;
			}
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
		Disjunction invalidation({});
		switch (optim.optim) {
		case Optim::SUBSET:
			unsatreached = invalidateSubset(invalidation.literals, optim);
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
				unsatreached = invalidateModel(invalidation) == SATVAL::UNSAT;
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
		internalAdd(Disjunction(savedinvalidation), getSolver().getBaseTheoryID(), getSolver());

		// If resetting state, also fix the optimization constraints to their optimal condition
		switch (optim.optim) {
		case Optim::SUBSET: {
			WLSet set(getSolver().newSetID());
			for (auto i = optim.to_minimize.cbegin(); i < optim.to_minimize.cend(); ++i) {
				set.wl.push_back( { *i, 1 });
			}
			internalAdd(set, getSolver().getBaseTheoryID(), getSolver());
			auto var = getSolver().newAtom();
			internalAdd(Disjunction({ mkPosLit(var) }), getSolver().getBaseTheoryID(), getSolver());
			internalAdd(Aggregate(mkPosLit(var), set.setID, _solutions->getBestValueFound(), AggType::CARD, AggSign::UB, AggSem::COMP, -1, false), getSolver().getBaseTheoryID(), getSolver());
			break;
		}
		case Optim::AGG: {
			auto agg = optim.agg_to_minimize;
			agg->setBound(AggBound(agg->getSign(), _solutions->getBestValueFound()));
			agg->reInitializeAgg();
			break;
		}
		case Optim::VAR: {
			internalAdd(Disjunction({ optim.var->getEQLit(_solutions->getBestValueFound()) }), getSolver().getBaseTheoryID(), getSolver());
			break;
		}
		}
	}

	return unsatreached && modelfound;
}

void ModelExpand::notifyCurrentOptimum(const Weight& value) const {
	printer->notifyCurrentOptimum(value);
}

/*
 * UnitPropagate
 */
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
		output << getSpace()->getTranslator()->toString(*i);
	}
	output << "\n";
	resman->close();
}
/*
 * Transform
 */
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
