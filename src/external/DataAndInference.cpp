#include "DataAndInference.hpp"

#include "Remapper.hpp"
#include "external/Translator.hpp"
#include "theorysolvers/PCSolver.hpp"
#include "modules/aggsolver/AggProp.hpp"
#include "datastructures/InnerDataStructures.hpp"
#include "modules/aggsolver/AggSet.hpp"
#include "external/SearchMonitor.hpp"
#include "constraintvisitors/FlatZincRewriter.hpp"
#include "Printer.hpp"
#include "ModelManager.hpp"

#include <map>
#include <vector>

using namespace std;
using namespace MinisatID;

Var VarCreation::createVar() {
	return remapper->getNewVar();
}

void Task::execute() {
	space->getEngine().finishParsing();
	innerExecute();
}
void Task::notifyTerminateRequested() {
	terminate = true;
	space->getEngine().notifyTerminateRequested();
}

ModelExpand::ModelExpand(Space* space, ModelExpandOptions options, const litlist& assumptions)
		: Task(space), _solutions(new ModelManager(options.savemodels)), _options(options), assumptions(assumptions), optim(Optim::NONE) {

}

ModelExpand::~ModelExpand(){
	delete(_solutions);
}


int ModelExpand::getNbModelsFound() const {
	return _solutions->getNbModelsFound();
}

PCSolver& ModelExpand::getSolver() const {
	return getSpace()->getEngine();
}

const SolverOption& ModelExpand::modes() const {
	return getSpace()->getOptions();
}

const modellist& ModelExpand::getSolutions() const {
	return _solutions->getModels();
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
	if (optim != Optim::NONE && _options.nbmodelstofind != 1) {
		throw idpexception("Finding multiple models can currently not be combined with optimization.\n");
	}

	litlist vecassumptions = assumptions;

	printSearchStart(clog, modes().verbosity);

	if (optim != Optim::NONE) {
		findOptimal(assumptions);
	} else {
		MXState moremodels = findNext(assumptions, _options);
		// TODO handle MXState::unknown?
		if (moremodels == MXState::UNSAT) {
			if (getNbModelsFound() == 0) {
				printNoModels(clog, modes().verbosity);
			} else {
				printNoMoreModels(clog, modes().verbosity);
			}
		}
	}

	printSearchEnd(clog, modes().verbosity);
}

//Translate into original vocabulary
vector<Literal> getBackMappedModel(const std::vector<Lit>& model, const Remapper& r) {
	vector<Literal> outmodel;
	for (auto i = model.cbegin(); i != model.cend(); ++i) {
		if (canBackMapLiteral(*i, r)) {
			outmodel.push_back(getBackMappedLiteral(*i, r));
		}
	}
	sort(outmodel.begin(), outmodel.end());
	return outmodel;
}
void addModelToSolution(const std::shared_ptr<InnerModel>& model, const Remapper& remapper, ModelManager& solution) {
	auto outmodel = new Model();
	outmodel->literalinterpretations = getBackMappedModel(model->litassignments, remapper);
	outmodel->variableassignments = model->varassignments;
	solution.addModel(outmodel);
}

void ModelExpand::addModel(std::shared_ptr<InnerModel> model) {
	addModelToSolution(model, getSpace()->getRemapper(), *_solutions);
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
	bool moremodels = true;
	while (moremodels && (options.nbmodelstofind == 0 || _solutions->getNbModelsFound() < options.nbmodelstofind)) {
		auto state = getSolver().solve(assmpt, true);
		if (state == l_Undef) {
			return MXState::UNKNOWN;
		}
		bool modelfound = state == l_True;

		if (not modelfound) {
			moremodels = false;
			break;
		}

		auto fullmodel = getSpace()->getEngine().getModel();
		addModel(fullmodel);

		// FIXME incorrect in the case of CP!
		// => first check whether there might be more CP models before backtracking completely!
		// Probably better refactor to put this deeper?
		/*#ifdef CPSUPPORT
				if(hasCPSolver()) {
					//Check for more models with different var assignment
					while(moremodels && (options.nbmodelstofind == 0 || getParent().getNbModelsFound() < options.nbmodelstofind)) {
						rClause confl = getCPSolver().findNextModel();
						if(confl!=nullPtrClause) {
							moremodels = false;
						} else {
							extractVarModel(fullmodel);
							getParent().addModel(*fullmodel);
						}
					}
				}
		#endif*/

		//Invalidate SAT model
		if (getSolver().getCurrentDecisionLevel() != assmpt.size()) { //choices were made, so other models possible
			InnerDisjunction invalidation;
			invalidate(invalidation.literals);
			moremodels = invalidateModel(invalidation.literals) == SATVAL::POS_SAT;
		} else {
			moremodels = false;
		}
	}

	return moremodels ? MXState::MODEL : MXState::UNSAT;
}

void ModelExpand::invalidate(litlist& clause) {
	// Add negation of model as clause for next iteration.
	// By default: by adding all choice literals
	auto v = getSolver().getDecisions();
	for (auto i = v.cbegin(); i < v.cend(); ++i) {
		clause.push_back(~(*i));
	}
}

/**
 * Returns false if invalidating the model leads to UNSAT, meaning that no more models are possible. Otherwise true.
 */
SATVAL ModelExpand::invalidateModel(const litlist& clause) {
	InnerDisjunction d;
	d.literals = clause;
	getSolver().backtrackTo(0); // Otherwise, clauses cannot be added to the sat-solver anyway

	if (modes().verbosity >= 3) {
		clog << "Adding model-invalidating clause: [ ";
		getSpace()->print(d.literals);
		clog << "]\n";
	}
	getSolver().add(d);
	return getSolver().satState();
}

// OPTIMIZATION METHODS
bool ModelExpand::invalidateSubset(litlist& invalidation, litlist& assmpt) {
	int subsetsize = 0;

	for (auto i = to_minimize.cbegin(); i < to_minimize.cend(); ++i) {
		auto lit = *i;
		if (getSolver().getModelValue(var(lit)) == l_True) {
			invalidation.push_back(~lit);
			++subsetsize;
		} else {
			assmpt.push_back(~lit);
		}
	}

	if (subsetsize == 0) {
		return true; //optimum has already been found!!!
	} else {
		return false;
	}
}

bool ModelExpand::invalidateValue(litlist& invalidation) {
	bool currentoptimumfound = false;

	for (uint i = 0; !currentoptimumfound && i < to_minimize.size(); ++i) {
		if (!currentoptimumfound && getSolver().getModelValue(var(to_minimize[i])) == l_True) {
			if (modes().verbosity >= 1) {
				clog << "> Current optimum found for: ";
				clog << getSpace()->print(to_minimize[i]);
				clog << "\n";
			}
			currentoptimumfound = true;
		}
		if (!currentoptimumfound) {
			invalidation.push_back(to_minimize[i]);
		}
	}

	if (invalidation.size() == 0) {
		return true; //optimum has already been found!!!
	} else {
		return false;
	}
}

/*
 * If the optimum possible value is reached, the model is not invalidated. Otherwise, unsat has to be found first, so it is invalidated.
 * TODO: add code that allows to reset the solver when the optimal value has been found, to search for more models with the same optimal value.
 * Borrow this code from savestate/resetstate/saveclauses for the modal solver
 *
 * Returns true if an optimal model was found
 */
void ModelExpand::findOptimal(const litlist& assmpt) {
	litlist currentassmpt = assmpt;

	bool modelfound = false, unsatreached = false;

	while (not unsatreached) {
		if (optim == Optim::AGG) {
			// NOTE: necessary to propagate the changes to the bound correctly
			if (agg_to_minimize->reInitializeAgg() == SATVAL::UNSAT) {
				unsatreached = true;
				continue;
			}
		}

		auto sat = getSolver().solve(currentassmpt, true);
		if (sat == l_False) {
			unsatreached = true;
			break;
		} else if (sat == l_Undef) {
			break;
		}
		modelfound = true;

		//Store current model in m before invalidating the solver
		auto m = getSolver().getModel();

		//invalidate the solver
		InnerDisjunction invalidation;
		switch (optim) {
		case Optim::LIST:
			unsatreached = invalidateValue(invalidation.literals);
			break;
		case Optim::SUBSET:
			currentassmpt.clear();
			unsatreached = invalidateSubset(invalidation.literals, currentassmpt);
			break;
		case Optim::AGG:
			unsatreached = invalidateAgg(invalidation.literals);
			break;
		case Optim::NONE:
			assert(false);
			break;
		}

		if (!unsatreached) {
			if (getSolver().getCurrentDecisionLevel() != currentassmpt.size()) { //choices were made, so other models possible
				unsatreached = invalidateModel(invalidation.literals) == SATVAL::UNSAT;
			} else {
				unsatreached = true;
			}
		}

		addModel(m);
	}

	if (unsatreached && modelfound) {
		_solutions->notifyOptimalModelFound();
	}

	// TODO support for finding more optimal models?
}

bool ModelExpand::invalidateAgg(litlist& invalidation) {
	//FIXME assert(isInitialized());
	auto agg = agg_to_minimize;
	auto s = agg->getSet();
	Weight value = s->getType().getValue(*s);

	printer->notifyCurrentOptimum(value);
	if (modes().verbosity >= 1) {
		clog << "> Current optimal value " << value << "\n";
	}

	agg->setBound(AggBound(agg->getSign(), value - 1));

	if (s->getType().getMinPossible(*s) == value) {
		return true;
	}

	HeadReason ar(*agg, mkNegLit(var(agg->getHead())));
	s->getProp()->getExplanation(invalidation, ar);

	return false;
}

void ModelExpand::addOptimization(Optim type, const litlist& literals) {
	if (optim != Optim::NONE) {
		throw idpexception(">> Only one optimization statement is allowed.\n");
	}

	optim = type;
	to_minimize = literals;
}

void ModelExpand::addAggOptimization(Agg* aggmnmz) {
	if (optim != Optim::NONE) {
		throw idpexception(">> Only one optimization statement is allowed.\n");
	}

	optim = Optim::AGG;
	agg_to_minimize = aggmnmz; //aggmnmz->getAgg().front();
}

void InnerMonitor::notifyMonitor(const Lit& propagation, int decisionlevel) {
	for (auto i = monitors.cbegin(); i < monitors.cend(); ++i) {
		(*i)->notifyPropagated(remapper->getLiteral(propagation), decisionlevel);
	}
}

void InnerMonitor::notifyMonitor(int untillevel) {
	for (auto i = monitors.cbegin(); i < monitors.cend(); ++i) {
		(*i)->notifyBacktracked(untillevel);
	}
}

void ModelExpand::notifyCurrentOptimum(const Weight& value) const {
	printer->notifyCurrentOptimum(value);
}

std::string MinisatID::printLiteral(const Literal& lit){
	stringstream ss;
	ss << (lit.hasSign()?"-":"") << lit.getValue();
	return ss.str();
}

litlist UnitPropagate::getEntailedLiterals(){
	getSolver().backtrackTo(assumptions.size()); // Backtrack to the latest assumption decision
	return getSolver().getTrail();
}
void UnitPropagate::innerExecute(){
	getSolver().solve(assumptions, true);
}

void Transform::innerExecute(){
	if(outputlanguage==OutputFormat::FZ){
		FlatZincRewriter fzrw(modes()); // TODO outputfile
		getSolver().accept(fzrw);
	}
	// TODO other languages
}
