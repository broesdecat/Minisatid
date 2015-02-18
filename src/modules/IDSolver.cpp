/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#include "modules/IDSolver.hpp"
#include "satsolver/heuristics/Heuristics.hpp"

#include "utils/Print.hpp"
#include "external/utils/ContainerUtils.hpp"

#include "theorysolvers/PCSolver.hpp"

#include "modules/SCCtoCNF.hpp"
#include "external/ConstraintAdditionInterface.hpp"

#include "utils/NumericLimits.hpp"

#include <cmath>

// TODO in fact, having a propagator per scc might seem more logical?
// FIXME an unwellfounded model does NOT mean that the definition is not total
// TODO only add one loopform at a time (save all lits, check next time first whether all are false, otherwise choose one more)

// FIXME, when finishparsing returns present=false, the IDSolver should be deleted. Currenlty it still exists and addrule can still be called
// (and isinitialized is still false because finishparsing was aborted)

using namespace std;
using namespace MinisatID;

#ifdef DEBUG
#define CHECKNOTUNSAT MAssert(getPCSolver().satState()!=SATVAL::UNSAT)
#define CHECK(unsat) MAssert(getPCSolver().satState()==SATVAL::UNSAT || not unsat)
#define CHECKSEEN for (auto i=defdVars.cbegin(); i!=defdVars.cend(); ++i) {\
		MAssert(seen(*i)==0);\
	}
#else
#define CHECKNOTUNSAT
#define CHECK(unsat)
#define CHECKSEEN
#endif

IDAgg::IDAgg(const Lit& head, AggBound b, AggSem sem, AggType type, const std::vector<WL>& origwls)
		: 	bound(b),
			head(head),
			sem(sem),
			index(-1),
			type(type),
			wls(origwls) {
	std::sort(wls.begin(), wls.end(), compareByWeights<WL>);
}

IDSolver::IDSolver(PCSolver* s, int definitionID)
		: 	Propagator(s, "definition"),
			definitionID(definitionID),
			needInit(true),
			defn_strategy(getPCSolver().modes().defn_strategy),
			minvar(0),
			nbvars(0),
			_seen(NULL),
			sem(getPCSolver().modes().defsem),
			posrecagg(false),
			mixedrecagg(false),
			posloops(true),
			negloops(true),
			backtracked(true),
			adaption_total(100),
			adaption_current(0),
			savedloopf({ }),
			twovalueddef(false) {

	if(getPCSolver().modes().lazy){
		defn_strategy = adaptive;
		adaption_total = 200;
	}

	getPCSolver().accept(this);
	getPCSolver().accept(this, EV_DECISIONLEVEL);
	getPCSolver().accept(this, EV_BACKTRACK);
	getPCSolver().accept(this, EV_MODELFOUND);
	// FIXME add when modes.lazy is true => getPCSolver().getNonConstOptions().defn_strategy = adaptive;
}

IDSolver::~IDSolver() {
	if (_seen != NULL) {
		delete (_seen);
	}
	deleteList<DefinedVar>(definitions);
}

void IDSolver::createDefinition(Atom head, PropRule* r, DefType type) {
	MAssert(not hasDefVar(head));
	defdVars.push_back(head);
	setDefVar(head, new DefinedVar(r, type));
	MAssert(isDefined(head));
}
void IDSolver::createDefinition(Atom head, IDAgg* agg) {
	MAssert(not hasDefVar(head));
	defdVars.push_back(head);
	setDefVar(head, new DefinedVar(agg));
}

int IDSolver::getNbOfFormulas() const {
	return defdVars.size() == 0 ? 0 : defdVars.size() * log((double) defdVars.size()) / log(2);
}

inline void IDSolver::addCycleSource(Atom v) {
	if (!isCS(v)) {
		isCS(v) = true;
		css.push_back(v);
	}
}
inline void IDSolver::clearCycleSources() {
	for (auto i = css.cbegin(); i < css.cend(); ++i) {
		isCS(*i) = false;
	}
	css.clear();
}

void IDSolver::adaptStructsToHead(Atom) {
	nbvars = nVars();
	definitions.resize(nbvars, NULL);
}

/**
 * First literal in ps is the head of the rule. It has to be present and it has to be positive.
 *
 * if no body literals: empty set conjunction is TRUE, empty set disjunction is FALSE!
 *
 * If DefType::CONJ, then all body literals are inverted to create the completion clause
 * else, the head atom is inverted for the completion
 *
 * If only one body literal, the clause is always made conjunctive (for algorithmic correctness later on), semantics are the same.
 */
void IDSolver::addFinishedRule(const TempRule& rule) {
	MAssert(not rule.isagg);
	auto conj = rule.conjunctive;
	auto head = rule.head;

	adaptStructsToHead(head);

	if (isDefined(head)) {
		std::stringstream ss;
		ss << "Multiple rules have the same head " << toString(head) << ", which is not allowed!\n";
		throw idpexception(ss.str());
	}

	if (rule.body.empty()) {
		return;
	}

	//clog <<"Added rule on " <<toString(head) <<"\n";

	conj = conj || rule.body.size() == 1; //rules with only one body atom are treated as conjunctive
	auto r = new PropRule(mkLit(head), rule.body);
	createDefinition(head, r, conj ? DefType::CONJ : DefType::DISJ);
}

void IDSolver::addFinishedDefinedAggregate(const TempRule& rule) {
	MAssert(rule.isagg);

	auto head = rule.head;
	adaptStructsToHead(head);
	if (isDefined(head)) {
		std::stringstream ss;
		ss << "Multiple rules have the same head " << toString(head) << ", which is not allowed!\n";
		throw idpexception(ss.str());
	}

	AggBound b(rule.inneragg->sign, rule.inneragg->bound);
	auto agg = new IDAgg(mkLit(head), b, rule.inneragg->sem, rule.inneragg->type, rule.innerset->getWL());
	if (isInitiallyJustified(*agg)) {
		delete (agg);
		return;
	}
	createDefinition(head, agg);
}

void IDSolver::addRuleSet(const std::vector<TempRule*>& rules) {
	for (auto i = rules.cbegin(); i < rules.cend(); ++i) {
		if ((*i)->isagg) {
			addFinishedDefinedAggregate(**i);
		} else {
			addFinishedRule(**i);
		}
	}
	needInit = true;
	adaption_current++;
	getPCSolver().acceptForPropagation(this, PRIORITY::SLOW);
}

void IDSolver::accept(ConstraintVisitor& visitor) {
	for (auto i = defdVars.cbegin(); i < defdVars.cend(); ++i) {
		if (isDefined(*i)) {
			auto defvar = getDefVar(*i);
			if (defvar->type() == DefType::AGGR) {
				auto rule = defvar->definedaggregate();
				auto setid = getPCSolver().newSetID();
				visitor.add(WLSet(setid, rule->getWL()));
				// TODO: leads to duplicate aggregates!
				visitor.add(
						Aggregate(rule->getHead(), setid, rule->getBound(), rule->getType(), rule->getSign(), AggSem::DEF, getDefinitionID(), true));
			} else {
				auto rule = defvar->definition();
				visitor.add(Rule(var(rule->getHead()), rule->getBody(), defvar->type() == DefType::CONJ, getDefinitionID(), true));
			}
		}
	}
}

/*
 * @PRE: aggregates have to have been finished
 */
void IDSolver::initialize() {
	needInit = false;
	if(adaption_current>adaption_total){
		adaption_total *= 2;
	}
	adaption_current=0;
	// NOTE can only initialize unfounded sets at level 0
	// FIXME improve this by only using root literals for simplification and to use a reverse trail
	if (getPCSolver().getCurrentDecisionLevel() != 0) {
		getPCSolver().backtrackTo(0);
	}

	//stepsTillInitialize = groundingSteps+100;
	//oneInitDone = true;
	MAssert(not getPCSolver().isUnsat());

	if (verbosity() > 0) {
		clog << ">>> Initializing inductive definition " << definitionID << "\n";
	}

	if (modes().lazy) {
		defdVars.clear();
		for (uint var = 0; var < definitions.size(); ++var) {
			if (isDefined(var)) {
				defdVars.push_back(var);
			}
		}
	}

	//LAZY initialization
	posloops = true;
	negloops = true;
	mixedrecagg = false;
	posrecagg = false;
	if (_seen != NULL) {
		delete (_seen);
	}
	_seen = new InterMediateDataStruct(nbvars, minvar);
	disj.clear();
	conj.clear();
	aggr.clear();
	disj.resize(nVars() * 2);
	conj.resize(nVars() * 2);
	aggr.resize(nVars() * 2);

	if (modes().defsem == DEF_COMP || defdVars.size() == 0) {
		if (not modes().lazy) {
			notifyNotPresent();
		} CHECKSEEN;
		return;
	}

	for (auto i = defdVars.cbegin(); i != defdVars.cend(); ++i) {
		MAssert(isDefined(*i));
		occ(*i) = NONDEFOCC;
	}

	if (verbosity() >= 1) {
		clog << "> Number of rules : " << defdVars.size() << ".\n";
	}

	generateSCCs();

	// Determine which literals should no longer be considered defined (according to the scc in the positive graph) + init occurs
	int atoms_in_pos_loops = 0;
	varlist reducedVars;
	for (auto i = defdVars.cbegin(); i < defdVars.cend(); ++i) {
		Atom v = (*i);

		bool addtonetwork = false;
		if (loopPossibleOver(v)) { //might be in pos loop
			++atoms_in_pos_loops;
			occ(v) = occ(v) == MIXEDLOOP ? BOTHLOOP : POSLOOP;
			addtonetwork = true;
		} else { //can never be in posloop
			if (occ(v) == NONDEFOCC) { //will not occur in a loop
				//clog <<getPrintableVar(v) <<" cannot be in any loop.\n";
				removeDefinition(v);
			} else if (occ(v) == MIXEDLOOP) { //might occur in a mixed loop
				//clog <<getPrintableVar(v) <<" can be in a mixed loop.\n";
				addtonetwork = true;
			}
		}

		if (addtonetwork) {
			//clog <<"Still defined: " <<toString(v) <<"\n";
			reducedVars.push_back(v);
			addToNetwork(v);
		}
	}
	defdVars.clear();
	defdVars.insert(defdVars.begin(), reducedVars.cbegin(), reducedVars.cend());

	if (atoms_in_pos_loops == 0) {
		posloops = false;
	}

	if (getSemantics() == DEF_STABLE) {
		negloops = false;
	}

	if (!posloops && !negloops) {
		if (not modes().lazy) {
			notifyNotPresent();
		}CHECKSEEN;
		return;
	}

	if (modes().bumpidonstart) {
		bumpHeadHeuristic();
	}

	bool unsat = getPCSolver().isUnsat();
	if (not unsat) {
		unsat = not simplifyGraph(atoms_in_pos_loops);
	}

	if (verbosity() >= 1) {
		clog << "> Number of recursive atoms in positive loops : " << atoms_in_pos_loops << ".\n";
		if (negloops) {
			clog << "> Mixed loops" << (mixedrecagg ? ", also over aggregates," : "") << " exist.\n";
		}
	}

	if (not unsat && modes().tocnf) {
		unsat = transformToCNF(sccroots) == SATVAL::UNSAT;
	}

	if (unsat) {
		getPCSolver().notifyUnsat();
	} else {
		CHECKSEEN;
	}
}

// NOTE: essentially, simplifygraph can be called anytime the level-0 interpretation has changed.
// In default model expansion, this turned out to be quite expensive, so it was disabled.
bool IDSolver::simplifyGraph(int& atomsinposloops) {
	CHECKNOTUNSAT;
	if (!posloops) {
		CHECKNOTUNSAT;
		return true;
	}

	//clog <<"Simplifying\n";

	varlist usedseen; //stores which elements in the "seen" datastructure we adapted to reset them later on
	for (auto i = defdVars.cbegin(); i < defdVars.cend(); ++i) {
		Atom v = (*i);

		justification(v).clear();

		if (isFalse(mkPosLit(v))) {
			continue;
		}
		switch (type(v)) {
		case DefType::DISJ:
		case DefType::AGGR:
			seen(v) = 1;
			break;
		case DefType::CONJ:
			seen(v) = definition(v)->size();
			break;
		}
		//clog <<"Counter for " <<toString(v) <<" is " <<seen(v) <<"\n";
		usedseen.push_back(v);
	}

// initialize a queue of literals that are safe with regard to cycle-freeness. (i.e.: either are not in justification, or are justified in a cycle-free way.)
	queue<Lit> propq;
	for (int i = 0; i < nVars(); ++i) {
		Lit l = mkNegLit(i);
		if (not isFalse(l)) {
			propq.push(l); // First negative literals are added that are not already false
		}
		l = mkPosLit(i);
		if (not isDefInPosGraph(i) && not isFalse(l)) {
			if (isDefined(var(l))) {
				seen(var(l)) = 0; //Mixed loop is justified, so seen is 0 (otherwise might find the same literal multiple times)
			}
			propq.push(l); // Then all non-false non-defined positive literals.
		}
	}

// propagate safeness to defined literals until fixpoint.
// While we do this, we build the initial justification.
	while (not propq.empty()) {
		Lit l = propq.front(); //only heads are added to the queue
		//clog <<"Propagating with " <<toString(l) <<"\n";
		MAssert(sign(l) || !isDefined(var(l)) || (seen(var(l))==0));
		propq.pop();

		litlist heads;
		vector<litlist> jstf;
		propagateJustificationDisj(l, jstf, heads);
		for (uint i = 0; i < heads.size(); ++i) {
			MAssert(jstf[i].size()==1);
			changejust(var(heads[i]), jstf[i]);
			//clog <<"Justified " <<toString(heads[i]) <<"\n";
			propq.push(heads[i]);
		}

		litlist heads2;
		vector<litlist> jstf2;
		propagateJustificationAggr(l, jstf2, heads2);
		for (uint i = 0; i < heads2.size(); ++i) {
			changejust(var(heads2[i]), jstf2[i]);
			//clog <<"Justified " <<toString(heads2[i]) <<"\n";
			propq.push(heads2[i]);
		}

		propagateJustificationConj(l, propq);
	}

	stringstream ss;
	if (verbosity() >= 2) {
		ss << "Initialization of justification makes these atoms false: [";
	}

	/**
	 * Goes through all definitions and checks whether they can still become true (if they have been
	 * justified). Otherwise, it is checked (overestimation) whether a negative loop might be possible.
	 * If this is not the case, the definition is removed from the data structures.
	 */
	varlist reducedVars;
	posrecagg = false;
	mixedrecagg = false;
	for (auto i = defdVars.cbegin(); i < defdVars.cend(); ++i) {
		Atom v = (*i);
		if (occ(v) == NONDEFOCC) {
			continue; // Not defined at the moment, but might be later on if lazy
		}
		auto lit = mkPosLit(v);
		if (seen(v) > 0 || isFalse(lit)) {
			if (verbosity() >= 2) {
				ss << " " << toString(lit);
			}
			if (isTrue(lit)) {
				if (verbosity() > 5) {
					clog << "True literal " << toString(lit) << " could not be justified under the current interpretation.\n";
				}
				return false;
			}
			if (isUnknown(lit)) {
				getPCSolver().setTrue(mkNegLit(v), this);
			}

			if (occ(v) == POSLOOP) {
				removeDefinition(v);
				--atomsinposloops;
			} else {
				occ(v) = MIXEDLOOP;
				reducedVars.push_back(v);
				if (type(v) == DefType::AGGR) {
					mixedrecagg = true;
				}
			}
		} else {
			reducedVars.push_back(v);
			if (type(v) == DefType::AGGR) {
				switch (occ(v)) {
				case MIXEDLOOP:
					mixedrecagg = true;
					break;
				case POSLOOP:
					posrecagg = true;
					break;
				case BOTHLOOP:
					mixedrecagg = true;
					posrecagg = true;
					break;
				case NONDEFOCC:
					break;
				}
			}
		}
	}
	defdVars.clear();
	defdVars.insert(defdVars.begin(), reducedVars.cbegin(), reducedVars.cend());

//reconstruct the disj and conj occurs with the reduced number of definitions
	disj.clear();
	conj.clear();
	aggr.clear();
	disj.resize(2 * nVars());
	conj.resize(2 * nVars());
	aggr.resize(2 * nVars());
	for (auto i = defdVars.cbegin(); i < defdVars.cend(); ++i) {
		Atom v = (*i);
		if (type(v) == DefType::CONJ || type(v) == DefType::DISJ) {
			auto dfn = *definition(v);
			for (auto litit = dfn.cbegin(); litit < dfn.cend(); ++litit) {
				if (*litit != dfn.getHead()) { //NOTE: don't look for a justification that is the head literal itself
					if (type(v) == DefType::DISJ) {
						disj.add(*litit, v);
					} else if (type(v) == DefType::CONJ) {
						conj.add(*litit, v);
					}
				}
			}
		} else {
			auto dfn = *aggdefinition(v);
			for (auto j = dfn.getWL().cbegin(); j < dfn.getWL().cend(); ++j) {
				aggr.add((*j).getLit(), v);
			}
		}
	}

//Reset the elements in "seen" that were changed
//NOTE: do not return before this call!
	for (auto i = usedseen.cbegin(); i < usedseen.cend(); ++i) {
		seen(*i) = 0;
	}

	if (verbosity() >= 2) {
		ss << " ]\n";
		clog << ss.str();
	}

	if (atomsinposloops == 0) {
		posloops = false;
	}

	if (!posloops && !negloops) {
		if (verbosity() >= 1) {
			clog << "> All recursive atoms falsified in initializations.\n";
		}
	}

#ifdef DEBUG
	if(verbosity()>=9) {
		printPosGraphJustifications();
	}
	int count = 0;
	for (auto i = defdVars.cbegin(); i < defdVars.cend(); ++i) {
		Atom var = *i;
		MAssert(hasDefVar(var));
		//MAssert(justification(var).size()>0 || type(var)!=DefType::DISJ || occ(var)==MIXEDLOOP); FIXME lazy grounding hack (because invar that def gets deleted)

		if(verbosity()>=9) {
			clog <<toString(var) <<"<-";
			bool begin = true;
			count++;
			for(auto i=justification(var).cbegin(); i!=justification(var).cend(); ++i) {
				if(!begin) {
					clog <<",";
				}
				begin = false;
				clog <<toString(*i);
			}
			clog <<";";
			if(count%30==0) {
				clog <<"\n";
			}
		}

		Lit l(mkPosLit(var));
		for (auto j = disj.occurs(l).cbegin(); j < disj.occurs(l).cend(); ++j) {
			MAssert(type(*j)==DefType::DISJ);
		}
		for (auto j = conj.occurs(l).cbegin(); j < conj.occurs(l).cend(); ++j) {
			MAssert(type(*j)==DefType::CONJ);
		}
		l = mkNegLit(var);
		for (auto j = disj.occurs(l).cbegin(); j < disj.occurs(l).cend(); ++j) {
			MAssert(type(*j)==DefType::DISJ);
		}
		for (auto j = conj.occurs(l).cbegin(); j < conj.occurs(l).cend(); ++j) {
			MAssert(type(*j)==DefType::CONJ);
		}
	}
#endif
	CHECKSEEN;

	return getPCSolver().satState() != SATVAL::UNSAT;
}

void IDSolver::generateSCCs() {
// Initialize scc of full dependency graph
//TODO remove nVars!
	vector<bool> incomp(nVars(), false);
	varlist stack;
	vector<int> visited(nVars(), 0); // =0 represents not visited; >0 corresponds to visited through a positive body literal, <0 through a negative body literal
	varlist mixedroots;
	sccroots.clear();
	varlist nodeinmixed;
	int counter = 1;

	for (auto i = defdVars.cbegin(); i < defdVars.cend(); ++i) {
		if (visited[(*i)] == 0) {
			visitFull((*i), incomp, stack, visited, counter, true, sccroots, mixedroots, nodeinmixed);
		}
	}

	if (mixedroots.size() == 0) {
		negloops = false;
	}

//all var in rootofmixed are the roots of mixed loops. All other are no loops (size 1) or positive loops

// Initialize scc of positive dependency graph
	for (auto i = nodeinmixed.cbegin(); i != nodeinmixed.cend(); ++i) {
		incomp[*i] = false;
		occ(*i) = MIXEDLOOP;
		visited[*i] = 0;
	}
	stack.clear();
	counter = 1;

	for (auto i = nodeinmixed.cbegin(); i != nodeinmixed.cend(); ++i) {
		if (visited[*i] == 0) {
			visit(*i, incomp, stack, visited, counter, sccroots);
		}
	}

	if (verbosity() > 20) {
		clog << "Printing mapping from variables to the ID of the SCC in which it occurs:\n";
		for (auto i = defdVars.cbegin(); i < defdVars.cend(); ++i) {
			clog << "SCC of " << toString(*i) << " is " << toString(scc(*i)) << ", ";
		}
		clog << "Ended printing sccs.\n";
	}
}

bool IDSolver::loopPossibleOver(Atom v) {
	DefType t = type(v);
	switch (t) {
	case DefType::DISJ:
	case DefType::CONJ:
		for (auto j = definition(v)->cbegin(); j < definition(v)->cend(); ++j) {
			Lit l = *j;
			if (inSameSCC(v, var(l))) {
				return true;
			}
		}
		break;
	case DefType::AGGR: {
		for (auto j = getSetLitsOfAggWithHeadBegin(v); j < getSetLitsOfAggWithHeadEnd(v); ++j) {
			if (inSameSCC(v, var((*j).getLit()))) { // NOTE: disregard sign here: set literals can occur both pos and neg in justifications.
				return true;
			}
		}
		break;
	}
	}
	return false;
}

void IDSolver::addToNetwork(Atom v) {
//IMPORTANT: also add mixed loop rules to the network for checking well-founded model
//could be moved to different datastructure to speed up
	switch (type(v)) {
	case DefType::DISJ:
		for (auto j = definition(v)->cbegin(); j < definition(v)->cend(); ++j) {
			Lit l = *j;
			if (l == definition(v)->getHead()) {
				continue;
			}
			disj.add(l, v);
		}
		break;
	case DefType::CONJ:
		for (auto j = definition(v)->cbegin(); j < definition(v)->cend(); ++j) {
			Lit l = *j;
			if (l == definition(v)->getHead()) {
				continue;
			}
			conj.add(l, v);
		}
		break;
	case DefType::AGGR:
		const auto& aggdef = *aggdefinition(v);
		for (auto j = aggdef.getWL().cbegin(); j != aggdef.getWL().cend(); ++j) {
			if (aggdef.hasLB()) { // NOTE: important: for aggregates with only POSITIVE aggregates which can only INCREASE when making those literals true.
				aggr.add((*j).getLit(), v);
			}
			if (aggdef.hasUB()) {
				aggr.add(~(*j).getLit(), v);
			}
		}
		switch (occ(v)) {
		case MIXEDLOOP:
			mixedrecagg = true;
			break;
		case POSLOOP:
			posrecagg = true;
			break;
		case BOTHLOOP:
			mixedrecagg = true;
			posrecagg = true;
			break;
		case NONDEFOCC:
			MAssert(false);
			break;
		}
		break;
	}
}

void IDSolver::bumpHeadHeuristic() {
//This heuristic on its own solves hamiltonian path for slow decay
	for (auto i = defdVars.cbegin(); i < defdVars.cend(); ++i) {
		const Atom& v = *i;
		if (isDefined(v) && type(v) == DefType::DISJ) {
			const PropRule& r = *definition(v);
			for (uint j = 0; j < r.size(); ++j) {
				getPCSolver().getHeuristic().notifyHead(var(r[j]));
			}
		}
	}
}

SATVAL IDSolver::transformToCNF(const varlist& sccroots) {
	bool unsat = false;
	map<Atom, std::vector<Atom> > root2sccs;
	for (auto root : sccroots) {
		if(not isDefined(root)){
			continue; // It might be that after simplification, some scc root is no longer defined.
		}
		bool hasaggs = false;
		for (auto head : defdVars) {
			if (scc(root) == scc(head)) {
				if (isDefinedByAggr(head)) {
					hasaggs = true;
					break;
				}
				root2sccs[root].push_back(head);
			}
		}
		if (hasaggs) {
			root2sccs.erase(root);
		}
	}
	for (auto root2scc : root2sccs) {
		vector<toCNF::Rule*> rules;
		for (auto head : root2scc.second) {
			litlist defbodylits, openbodylits;
			auto proprule = getDefVar(head)->definition();
			for (auto bodylit = proprule->cbegin(); bodylit != proprule->cend(); ++bodylit) {
				if (not sign(*bodylit) && hasDefVar(var(*bodylit)) && scc(var(*bodylit)) == scc(root2scc.first)) {
					defbodylits.push_back(*bodylit);
				} else {
					openbodylits.push_back(*bodylit);
				}
			}
			auto rule = new toCNF::Rule(isDisjunctive(head), head, defbodylits, openbodylits);
			rules.push_back(rule);
		}
		unsat = not toCNF::transformSCCtoCNF(getPCSolver(), rules);
		deleteList<toCNF::Rule>(rules);
	}
	if (not negloops && not modes().lazy) { // FIXME if negloops possible, ONLY do wellfoundedness check!
		notifyNotPresent();
	}
	return unsat ? SATVAL::UNSAT : SATVAL::POS_SAT;
}

void IDSolver::removeDefinition(Atom head) {
	if (modes().lazy) { // NOTE: it might not currently be in a loop, but might be in future when more rules are added
		return;
	}
	delete getDefVar(head);
	setDefVar(head, NULL);
}

/**
 * Executes the basic tarjan algorithm for finding strongly connected components (scc). It does this in the FULL dependency graph
 * @pre: only call it on defined nodes that are not already in a found scc
 * @post: root will be a partition that will be the exact partition of SCCs, by setting everything on the stack to the same root in the end
 * @post: the scc will be denoted by the variable in the scc which was visited first
 */
void IDSolver::visitFull(Atom i, vector<bool> &incomp, varlist &stack, varlist &visited, int& counter, bool throughPositiveLit, varlist& posroots,
		varlist& rootofmixed, varlist& nodeinmixed) {
	MAssert(!incomp[i]);
	MAssert(isDefined(i));
	++counter;
	visited[i] = throughPositiveLit ? counter : -counter;
	scc(i) = i;
	stack.push_back(i);

	switch (type(i)) {
	case DefType::DISJ:
	case DefType::CONJ: {
		auto r = definition(i);
		for (uint j = 0; j < r->size(); ++j) {
			auto l = (*r)[j];
			auto w = var(l);
			if (!isDefined(w)) {
				continue;
			}

			if (visited[w] == 0) {
				visitFull(w, incomp, stack, visited, counter, isPositive(l), posroots, rootofmixed, nodeinmixed);
			} else if (!incomp[w] && !isPositive(l) && visited[i] > 0) {
				visited[i] = -visited[i];
			}
			if (!incomp[w] && abs(visited[scc(i)]) > abs(visited[scc(w)])) {
				scc(i) = scc(w);
			}
		}
		break;
	}
	case DefType::AGGR: {
		for (auto j = getSetLitsOfAggWithHeadBegin(i); j < getSetLitsOfAggWithHeadEnd(i); ++j) {
			auto w = var((*j).getLit());
			if (!isDefined(w)) {
				continue;
			}

			if (visited[w] == 0) {
				visitFull(w, incomp, stack, visited, counter, false /*Over-approximation of negative occurences*/, posroots, rootofmixed, nodeinmixed);
			} else if (!incomp[w] && visited[i] > 0) { // Over-approximation of negative occurences
				visited[i] = -visited[i];
			}
			if (!incomp[w] && abs(visited[scc(i)]) > abs(visited[scc(w)])) {
				scc(i) = scc(w);
			}
		}
		break;
	}
	}

	if (scc(i) == i) {
		varlist sccs;
		bool mixed = false;
		int w;
		do {
			w = stack.back();
			stack.pop_back();
			visited[w] < 0 ? mixed = true : true;
			scc(w) = i; //these are the found sccs
			sccs.push_back(w);
			incomp[w] = true;
		} while (w != i);
		if (mixed && sccs.size() > 1) {
			rootofmixed.push_back(i);
			nodeinmixed.insert(nodeinmixed.begin(), sccs.cbegin(), sccs.cend());
		} else {
			posroots.push_back(i);
		}
	}
}

/**
 * Executes the basic tarjan algorithm for finding strongly connected components (scc). It does this in the
 * POSITIVE dependency graph.
 * @pre: only call it on defined nodes that are not already in a found scc
 * @post: root will be a partition that will be the exact partition of SCCs, by setting everything on the stack to the same root in the end
 * @post: the scc will be denoted by the variable in the scc which was visited first
 */
void IDSolver::visit(Atom i, vector<bool> &incomp, varlist &stack, varlist &visited, int& counter, varlist& roots) {
	MAssert(scc(i)>=0 && scc(i)<nbvars);
	MAssert(!incomp[i]);
	visited[i] = ++counter;
	scc(i) = i;
	stack.push_back(i);

	switch (type(i)) {
	case DefType::DISJ:
	case DefType::CONJ: {
		auto r = definition(i);
		for (uint j = 0; j < r->size(); ++j) {
			auto l = (*r)[j];
			auto w = var(l);
			if (isDefined(w) && i != w && isPositive(l)) {
				if (visited[w] == 0) {
					visit(w, incomp, stack, visited, counter, roots);
				}
				if (!incomp[w] && visited[scc(i)] > visited[scc(w)]) {
					scc(i) = scc(w);
				}
			}
		}
		break;
	}
	case DefType::AGGR: {
		//TODO this can be optimized by using another method which only returns literals possibly in the positive dependency graph.
		for (auto j = getSetLitsOfAggWithHeadBegin(i); j < getSetLitsOfAggWithHeadEnd(i); ++j) {
			auto w = var((*j).getLit());
			if (!isDefined(w)) {
				continue;
			}

			if (visited[w] == 0) {
				visit(w, incomp, stack, visited, counter, roots);
			}
			if (!incomp[w] && visited[scc(i)] > visited[scc(w)]) {
				scc(i) = scc(w);
			}
		}
		break;
	}
	}

	if (scc(i) == i) {
		int w;
		roots.push_back(i);
		do {
			w = stack.back();
			stack.pop_back();
			scc(w) = i; //these are the found sccs
			incomp[w] = true;
		} while (w != i);
	}
}

/**
 * propagate the fact that w has been justified.
 *
 * Return all newly justified head in heads
 * Return all justification of those justified heads in jstf
 * Adapt nb_body... when some element has been justified
 */
void IDSolver::propagateJustificationDisj(const Lit& l, vector<litlist>& jstf, litlist& heads) {
	auto dd = disj.occurs(l);
	for (auto i = dd.cbegin(); i < dd.cend(); ++i) {
		auto v = *i;
		if (isFalse(mkPosLit(v)) || seen(v) == 0) {
			continue;
		}
		seen(v) = 0;
		heads.push_back(mkPosLit(v));
		jstf.push_back( { l });
	}
}

void IDSolver::propagateJustificationConj(const Lit& l, std::queue<Lit>& heads) {
	const varlist& ll = conj.occurs(l);
	for (auto i = ll.cbegin(); i < ll.cend(); ++i) {
		const Atom& v = *i;
		if (isFalse(mkPosLit(v)) || seen(v) == 0) {
			continue;
		}
		//clog <<"Reducing counter of " <<toString(v) <<"\n";
		seen(v)--;if
(		seen(v) == 0) {
			//clog <<"Justified " <<toString(v) <<"\n";
			heads.push(mkPosLit(v));
		}
	}
}

void IDSolver::propagateJustificationConj(const Lit& l, litlist& heads) {
	const varlist& ll = conj.occurs(l);
	for (auto i = ll.cbegin(); i < ll.cend(); ++i) {
		const Atom& v = *i;
		if (isFalse(mkPosLit(v)) || seen(v) == 0) {
			continue;
		}
		seen(v)--;if
(		seen(v) == 0) {
			heads.push_back(mkPosLit(v));
		}
	}
}

void IDSolver::propagateJustificationAggr(const Lit& l, vector<litlist>& jstfs, litlist& heads) {
	for (auto i = aggr.occurs(l).cbegin(); i < aggr.occurs(l).cend(); ++i) {
		const IDAgg& agg = *aggdefinition(*i);
		if (isFalse(agg.getHead())) {
			continue;
		}

		Atom head = var(agg.getHead());
		if (seen(head) > 0) { //only check its body for justification when it has not yet been derived
			litlist jstf;
			varlist nonjstf;

			if (canJustifyHead(agg, jstf, nonjstf, *_seen, false)) {
				//clog <<"Justified " <<toString(mkPosLit(head)) <<"\n";
				seen(head) = 0;
				heads.push_back(mkLit(head, false));
				jstfs.push_back(jstf);
			}
		}
	}
}

/*
 * IMPORTANT: should ONLY be called after all possible other propagations have been done:
 * the state has to be stable for both aggregate and unit propagations
 */
rClause IDSolver::notifypropagate() {
	CHECKNOTUNSAT;
	if(not shouldCheckPropagation()){
		CHECKNOTUNSAT; // NOTE: no seen guarantee, as initialization might not have been done
		return nullPtrClause;
	}
	if(needInit) {
		initialize();
		if (getPCSolver().isUnsat()) {
			return getPCSolver().createClause(Disjunction({ }), true);
		}
	}
	CHECKSEEN;CHECKNOTUNSAT;

	// There was an unfounded set saved which might not have been completely propagated by unit propagation
	// So check if there are any literals unknown and add more loopformulas
	if (savedufs.size() != 0) {
		for (auto i = savedufs.cbegin(); i != savedufs.cend(); ++i) {
			if (!isFalse(mkPosLit(*i))) {
				Lit l = mkNegLit(*i);
				addLoopfClause(l, savedloopf);
				CHECKSEEN;CHECKNOTUNSAT;
				return nullPtrClause;
			}
		}
		savedufs.clear(); //none found
	}

	if (not posloops) {
		CHECKSEEN;CHECKNOTUNSAT;
		return nullPtrClause;
	}

	findCycleSources();

	if (css.empty()) {
		CHECKSEEN;CHECKNOTUNSAT;
		return nullPtrClause;
	}

	uint64_t old_justify_calls = stats.justify_calls;

	std::set<Atom> ufs;
	rClause confl = nullPtrClause;
	bool ufs_found = false;
	for (auto j = css.cbegin(); confl == nullPtrClause && j < css.cend(); ++j) {
		if (isCS(*j)) {
			ufs_found = unfounded(*j, ufs);
			if (ufs_found) {
				if (verbosity() >= 2) {
					clog << "Found an unfounded set of size " << ufs.size() << ": {";
					for (auto it = ufs.cbegin(); it != ufs.cend(); ++it) {
						clog << " " << toString(*it);
					}
					clog << " }.\n";
				}
				++stats.cycles;
				stats.cycle_sizes += ufs.size();
				if (defn_strategy == adaptive) {
					++adaption_current; // This way we make sure that if adaption_current > adaption_total, this decision level had indirect propagations.
				}
				confl = assertUnfoundedSet(ufs);
			}
		}
	}

	// stats.justifiable_cycle_sources += ufs_found ? (j - 1) : j; // This includes those that are removed inside "unfounded".
	stats.succesful_justify_calls += (stats.justify_calls - old_justify_calls);

	if (confl == nullPtrClause) { // Found a witness justification.
		if (defn_strategy == adaptive) {
			if (adaption_current == adaption_total) {
				++adaption_total; // Next time, skip one decision level extra.
			} else {
				adaption_total--;
			}
			if (adaption_total < 0) {
				adaption_total = 0;
			}
			adaption_current = 0;
		}
	}

	CHECKSEEN;
	return confl;
}

// Return true if indirectpropagation is necessary. This is certainly necessary if the state is two-valued or if the strategy is always.
bool IDSolver::shouldCheckPropagation() {
	bool propagate = true;
	// if not always and state is three-valued.
	if (defn_strategy != always && not definitionIsTwovalued()) {
		if (getPCSolver().modes().defn_strategy == lazy) {
			propagate = false;
		}
		if (defn_strategy == adaptive && adaption_current < adaption_total) {
			++adaption_current;
			propagate = false;
		}
	}
	return propagate;
}

rClause IDSolver::notifyFullAssignmentFound() {
	twovalueddef = true;
	auto confl = notifypropagate();
	MAssert(not needInit);
	if (confl == nullPtrClause) {
		MAssert(not posloops || isCycleFree());
		if (getSemantics() == DEF_WELLF) {
			confl = isWellFoundedModel();
		}
	}
	twovalueddef = false; // NOTE: Just used for certainly running propagation, even if def_search==lazy
	return confl;
}

void IDSolver::notifyNewDecisionLevel() {
	if (posloops && defn_strategy != adaptive && !isCycleFree()) {
		throw idpexception("Positive justification graph is not cycle free!\n");
	}
}

void IDSolver::notifyBacktrack(int untillevel, const Lit& decision) {
	backtracked = true;
	Propagator::notifyBacktrack(untillevel, decision);
}

/**
 * Cycle sources are the defined variables that have lost support during the
 * preceding unit propagations, and for which a simple supporting replacement
 * justification may not be cycle-free.
 */
void IDSolver::findCycleSources() {
	clearCycleSources();

	if (not backtracked || defn_strategy == always) {
		while (hasNextProp()) {
			Lit l = getNextProp(); //l has become true, so find occurrences of not l
			MAssert(value(not l)==l_False);
			if (nbvars <= var(l)) {
				continue;
			}

			//TODO should check whether it is faster to use a real watched scheme here: go from justification to heads easily,
			//so this loop only goes over literal which are really justifications
			const auto& ds = disj.occurs(not l);
			for (auto j = ds.cbegin(); j < ds.cend(); ++j) {
				checkJustification(*j);
			}

			const auto& heads = getDefAggHeadsWithBodyLit(var(not l));
			for (auto j = heads.cbegin(); j < heads.cend(); ++j) {
				if (hasDefVar(*j)) {
					checkJustification(*j);
				}
			}
		}
	} else { //Only if not always and backtracked
		// NOTE: with a clever trail system, we could even after conflicts avoid having to look at all rules.
		backtracked = false;
		for (auto i = defdVars.cbegin(); i < defdVars.cend(); ++i) {
			if (type(*i) == DefType::DISJ || type(*i) == DefType::AGGR) {
				checkJustification(*i);
			}
		}
	}
	if (verbosity() > 3) {
		clog << ">>> Found " << css.size() << " possible cycle sources: ";
		for (auto i = css.cbegin(); i < css.cend(); ++i) {
			clog << " " << toString(*i);
		}
		clog << ".\n";
	}
	++stats.nb_times_findCS;
	stats.cycle_sources += css.size();
}

void IDSolver::checkJustification(Atom head) {
	if (!isDefInPosGraph(head) || isFalse(mkPosLit(head)) || isCS(head)) {
		return;
	}

	bool justfalse = false;
	for (uint i = 0; !justfalse && i < justification(head).size(); ++i) {
		if (isFalse(justification(head)[i])) {
			justfalse = true;
		}
	}
	if (!justfalse) {
		return;
	}

	//Incorrect to prune out heads in which Lit is not the justification

	//Possible heuristic: getPCSolver().varBumpActivity(head);

	litlist jstf;
	bool external = true;

	if (type(head) == DefType::DISJ) {
		findJustificationDisj(head, jstf);
		MAssert(jstf.size()>0);
	} else {
		MAssert(type(head)==DefType::AGGR);
		findJustificationAggr(head, jstf);
	}
	for (uint i = 0; external && i < jstf.size(); ++i) {
		if (isDefined(var(jstf[i])) && inSameSCC(head, var(jstf[i])) && isPositive(jstf[i])) {
			external = false;
		}
	}
	if (external) {
		changejust(head, jstf);
	} else {
		addCycleSource(head);
	}
}

/**
 * Looks for a justification for the given var. Attempts to find one that is not within the same positive dependency
 * graph scc (and certainly not false).
 */
void IDSolver::findJustificationDisj(Atom v, litlist& jstf) {
	const PropRule& c = *definition(v);
	int pos = -1;
	for (uint i = 0; i < c.size(); ++i) {
		if (!isFalse(c[i])) {
			pos = i;
			if (!inSameSCC(v, var(c[i])) || !isPositive(c[i]) || !isDefined(var(c[i]))) {
				break; //external justification is preferred.
			}
		}
	}
	MAssert(pos>=0);
	jstf.push_back(c[pos]);
}

/**
 * A loop is never introduced into the justification. If from the cycle source, no loop can be found,
 * the justification of the cycle source can be safely changed. If a loop is found, the cycle source becomes
 * false, so its justification can be kept to the original one, which will be correct when backtracking.
 */
bool IDSolver::unfounded(Atom cs, std::set<Atom>& ufs) {
	++stats.justify_calls;
	varlist tmpseen; // use to speed up the cleaning of data structures in "Finish"
	queue<Atom> q;
	Atom v;

#ifdef DEBUG
	for (auto i=defdVars.cbegin(); i!=defdVars.cend(); ++i) { //seen should have been erased
		MAssert(seen(*i)==0);
	}
#endif

	markNonJustified(cs, tmpseen);
	bool csisjustified = false;

	seen(cs) = 1; //no valid justification can be created just from looking at the body literals
	tmpseen.push_back(cs);

	if (verbosity() > 9) {
		for (auto i = defdVars.cbegin(); i < defdVars.cend(); ++i) {
			if (isJustified(*_seen, *i)) {
				clog << "Still justified " << toString(*i) << "\n";
			}
		}
	}

	q.push(cs);
	ufs.clear();
	ufs.insert(cs);
	while (!csisjustified && q.size() > 0) {
		v = q.front();
		q.pop();
		if (isJustified(*_seen, v)) {
			continue;
		}
		if (directlyJustifiable(v, ufs, q)) {
			if (verbosity() > 5) {
				clog << "Can directly justify " << toString(v) << "\n";
			}
			if (propagateJustified(v, cs, ufs)) {
				csisjustified = true;
			}
		}
	}

	for (uint i = 0; i < tmpseen.size(); ++i) {
		seen(tmpseen[i]) = 0;
	}

#ifdef DEBUG
	for (auto i=defdVars.cbegin(); i!=defdVars.cend(); ++i) { //seen should have been erased
		MAssert(seen(*i)==0);
	}
#endif

	if (!csisjustified) {
		MAssert(ufs.size() > 0);
		// The ufs atoms form an unfounded set. 'cs' is in it.
		return true;
	} else {
		ufs.clear();
		return false;
	}
}

/**
 * Important: to justify a head, often several body literals have to become FALSE
 * For such literals, they have to be justified if they are NEGATIVE
 *
 * Also, if a literal has to become FALSE, its INVERSION should be added to the justification!
 */
/**
 * seen is used as a justification mark/counter:
 *
 * seen==0 || negative body literal <=> justified
 */
inline bool IDSolver::isJustified(const InterMediateDataStruct& currentjust, Lit x) const {
	return isJustified(currentjust, var(x)) || !isPositive(x);
}
inline bool IDSolver::isJustified(const InterMediateDataStruct& currentjust, Atom x) const {
	return currentjust.hasElem(x) && currentjust.getElem(x) == 0;
}
inline bool IDSolver::oppositeIsJustified(const InterMediateDataStruct& currentjust, const WL& l, bool real) const {
	if (real) {
		return value(l.getLit()) != l_True;
	} else {
		return value(l.getLit()) != l_True && (!sign(l.getLit()) || isJustified(currentjust, var(l.getLit())));
	}
}
inline bool IDSolver::isJustified(const InterMediateDataStruct& currentjust, const WL& l, bool real) const {
	if (real) {
		return value(l.getLit()) != l_False;
	} else {
		return value(l.getLit()) != l_False && (sign(l.getLit()) || isJustified(currentjust, var(l.getLit())));
	}
}

/**
 * Checks whether there is a justification for v given the current justification counters
 */
bool IDSolver::findJustificationDisj(Atom v, litlist& jstf, varlist& nonjstf) {
	const PropRule& c = *definition(v);
	bool externallyjustified = false;
	seen(v) = 1;
	int pos = -1;
	for (uint i = 0; !externallyjustified && i < c.size(); ++i) {
		if (c.getHead() == c[i]) {
			continue;
		}

		if (!isFalse(c[i])) {
			if (!isPositive(c[i]) || seen(var(c[i])) == 0) {
				if (!inSameSCC(v, var(c[i]))) {
					externallyjustified = true;
					pos = i;
				} else {
					pos = i;
				}
			} else {
				nonjstf.push_back(var(c[i]));
			}
		}
	}
	if (pos >= 0) {
		jstf.push_back(c[pos]);
		seen(v) = 0;
	}
	return seen(v) == 0;
}

bool IDSolver::findJustificationConj(Atom v, litlist&, varlist& nonjstf) {
	const PropRule& c = *definition(v);
	seen(v) = 0;
	for (uint i = 0; i < c.size(); ++i) {
		if (isPositive(c[i]) && seen(var(c[i])) != 0) {
			++seen(v);
			nonjstf.push_back(var(c[i]));
		}
	}
	return seen(v) == 0;
}

bool IDSolver::findJustificationAggr(Atom v, litlist& jstf, varlist& nonjstf) {
	seen(v) = 1; //used as boolean (0 is justified, 1 is not)
	if (directlyJustifiable(v, jstf, nonjstf, *_seen)) {
		seen(v) = 0;
	}
	return seen(v) == 0;
}

/**
 * If the rule with head v can be justified, do that justification.
 * Otherwise, add all nonjustified body literals to the queue that have to be propagated (no negative body literals in a rule)
 *
 * @Post: v is now justified if a justification can be found based on the current seen vector
 * @Returns: true if v is now justified
 */
bool IDSolver::directlyJustifiable(Atom v, std::set<Atom>& ufs, queue<Atom>& q) {
	litlist jstf;
	varlist nonjstf;
	bool justified;

	switch (type(v)) {
	case DefType::CONJ:
		justified = findJustificationConj(v, jstf, nonjstf);
		break;
	case DefType::DISJ:
		justified = findJustificationDisj(v, jstf, nonjstf);
		break;
	case DefType::AGGR:
		justified = findJustificationAggr(v, jstf, nonjstf);
		break;
	default:
		MAssert(false);
		throw idpexception("The program tried to justify a rule that was not DefType::AGGR, DefType::DISJ or DefType::CONJ.\n");
	}
	if (justified) {
		MAssert(jstf.size()>0);
		changejust(v, jstf);
	} else {
		/*
		 * For conjunctive rules, it is not necessary to add all non-justified literals to the queue:
		 * one would be enough, as in the end all will have to be justified. Such a chosen literal would
		 * act as a watched literal: as long as it is not justified, the head cannot be justified. When it
		 * becomes justified, it should be checked whether there is another one not justified, which becomes
		 * the new watch.
		 * Maarten had such a "guards" system in the original code, but he claimed it complicated the code and
		 * had only a slight performance advantage and only on some benchmarks. It is commented in his original code.
		 */
		for (uint i = 0; i < nonjstf.size(); ++i) {
			MAssert(!isJustified(*_seen, nonjstf[i]));
			if (inSameSCC(nonjstf[i], v)) {
				if (ufs.insert(nonjstf[i]).second) { //set insert returns true (in second) if the insertion worked (no duplicates)
					q.push(nonjstf[i]);
				}
			}
		}
	}
	return isJustified(*_seen, v);
}

/**
 * Propagate the fact that v has been justified.
 *
 * Returns true if cs is now justified (and no longer a cycle source)
 */
bool IDSolver::propagateJustified(Atom v, Atom cs, std::set<Atom>& ufs) {
	varlist justifiedq;
	justifiedq.push_back(v); // literals that have to be justified
	while (justifiedq.size() > 0) {
		Atom k = justifiedq.back();
		justifiedq.pop_back();

		// Make it justified.
		ufs.erase(k);

		isCS(k) = false;
		++stats.cs_removed_in_justify;

		if (k == cs) {
			return true;
		}

		Lit bdl = mkPosLit(k);

		litlist heads;
		vector<litlist> jstf;
		propagateJustificationDisj(bdl, jstf, heads);
		propagateJustificationAggr(bdl, jstf, heads);

		for (uint i = 0; i < heads.size(); ++i) {
			MAssert(jstf[i].size()>0);
			changejust(var(heads[i]), jstf[i]);
			justifiedq.push_back(var(heads[i]));
			if (verbosity() > 5) {
				clog << "justified " << toString(var(heads[i])) << "\n";
			}
		}

		heads.clear();
		propagateJustificationConj(bdl, heads);
		for (uint i = 0; i < heads.size(); ++i) {
			justifiedq.push_back(var(heads[i]));
			if (verbosity() > 5) {
				clog << "justified " << toString(var(heads[i])) << "\n";
			}
		}
	}
	return false;
}

// Change sp_justification: v is now justified by j.
void IDSolver::changejust(Atom v, litlist& just) {
	MAssert(just.size()>0 || type(v)==DefType::AGGR);
	//justification can be empty for aggregates
	justification(v) = just;
	for (uint i = 0; i < just.size(); ++i) {
		getPCSolver().accept(this, not just[i], SLOW);
	}
}

/**
 * Given an unfounded sets, constructs the loop formula:
 * the set of all relevant external literals of the rules with heads in the unfounded set.
 */
void IDSolver::addExternalDisjuncts(const std::set<Atom>& ufs, litlist& loopf) {
#ifdef DEBUG
	MAssert(loopf.size()==1); //Space for the head/new variable
	for (auto i=defdVars.cbegin(); i!=defdVars.cend(); ++i) { //seen should be cleared
		MAssert(seen(*i)==0);
	}
#endif

	//In seen, we store literals that have been added to the loopf or found not to belong in it.
	//seen(A)==1 indicates that A has been added
	//seen(A)==2 indicates that not A has been added
	//Both can be added once, because of the assumption that a rule has been simplified to only contain any of them once

	for (std::set<Atom>::const_iterator tch = ufs.cbegin(); tch != ufs.cend(); ++tch) {
		switch (type(*tch)) {
		case DefType::CONJ: //
			break;
		case DefType::DISJ: {
			const PropRule& c = *definition(*tch);
			for (uint i = 0; i < c.size(); ++i) {
				Lit l = c[i];
				if ((!isDefined(var(l)) || seen(var(l)) != (isPositive(l) ? 2 : 1)) && ufs.find(var(c[i])) == ufs.cend()) {
					MAssert(isFalse(l));
					loopf.push_back(l);
					seen(var(l)) = (isPositive(l) ? 2 : 1);
				}
			}
			break;
		}
		case DefType::AGGR:
			addExternalLiterals(*tch, ufs, loopf, *_seen);
			break;
		default:
			MAssert(false);
			throw idpexception("Only DefType::AGGR, DefType::CONJ or DefType::DISJ should be checked for external disjuncts!\n");
			break;
		}
	}

	for (uint i = 1; i < loopf.size(); ++i) {
		seen(var(loopf[i])) = 0;
	}
	stats.extdisj_sizes += loopf.size() - 1;
}

/**
 * If an atom of 'ufs' was already true, return a loop formula for this (one such) atom as conflicting clause.
 * Otherwise, add a loop formula for each atom in ufs, enqueue the negation of
 * each of those atoms, and return NULL.
 * For each atom in UFS that is false, don't do anything
 *
 * Loop formulas are created in the form
 * UFSLITERAL IMPLIES DefType::DISJUNCTION(external disjuncts)
 *
 * Returns a non-owning pointer
 */
rClause IDSolver::assertUnfoundedSet(const std::set<Atom>& ufs) {
	auto placeholderlit = mkNegLit(getMaxElem<int>());
	MAssert(!ufs.empty());

	// Create the loop formula: add the external disjuncts (first element will be filled in later).
	Disjunction loopf({ placeholderlit });
	addExternalDisjuncts(ufs, loopf.literals);

	// Check if any of the literals in the set are already true, which leads to a conflict.
	for (auto tch = ufs.cbegin(); tch != ufs.cend(); ++tch) {
		if (isTrue(mkPosLit(*tch))) {
			loopf.literals[0] = mkNegLit(*tch); //negate the head to create a clause
			rClause c = getPCSolver().createClause(loopf, true);
			getPCSolver().addConflictClause(c);
			++stats.justify_conflicts;
			if (verbosity() >= 2) {
				clog << "Adding conflicting loop formula: [ ";
				MinisatID::toString(c, getPCSolver());
				clog << "].\n";
			}
			//reportf("Conflicting unfounded set found.\n");
			return c;
		}
	}

	//Clasp only adds one asserting clause, assuming the other ones will be propagated.
	//There might be multiple loops => solution: save unfounded set and if propagate is called again and no backtrack has occurred, check if all have been propagated to be false, otherwise, add more clauses
	if (getPCSolver().modes().selectOneFromUFS) {
		savedufs = ufs;
		savedloopf = loopf;
		auto l = mkNegLit(*ufs.cbegin());
		addLoopfClause(l, loopf);
	} else {
		// No conflict: then enqueue all facts and their loop formulas.
		if ((long) (loopf.literals.size() * ufs.size()) > modes().ufsvarintrothreshold) {
			//introduce a new var to represent all external disjuncts: v <=> \bigvee external disj
			auto v = getPCSolver().newAtom();
			if (verbosity() >= 2) {
				clog << "Adding new variable " << toString(v) << "for a ufs of size " << ufs.size() << " and " << loopf.literals.size()
						<< " external disjuncts.\n";
			}

			// not v \vee \bigvee\extdisj{L}
			addLoopfClause(mkNegLit(v), loopf);

			// \forall d \in \extdisj{L}: not d \vee v
			// UNSAT core extraction correct because of rule rewriting earlier on.
			Disjunction binaryclause({ placeholderlit, mkPosLit(v) });
			for (uint i = 1; i < loopf.literals.size(); ++i) {
				addLoopfClause(not loopf.literals[i], binaryclause);
			}

			loopf.literals = litlist(2);

			//the end loop formula just contains v
			loopf.literals[1] = mkPosLit(v);
		}

		for (auto tch = ufs.cbegin(); tch != ufs.cend(); ++tch) {
			auto l = mkNegLit(*tch);
			addLoopfClause(l, loopf);
		}
	}

	return nullPtrClause;
}

//Should make l false in the process
void IDSolver::addLoopfClause(Lit l, Disjunction& lits) {
	lits.literals[0] = l;

	if (getPCSolver().modes().idclausesaving > 0) {
		if (value(lits.literals[0]) == l_Undef) {
#ifdef DEBUG
			for(uint i=1; i<lits.literals.size(); ++i) {
				MAssert(value(lits.literals[i])!=l_Undef);
				MAssert(getPCSolver().assertedBefore(var(lits.literals[i]), var(l)));
			}
#endif

			reason(var(l)) = lits.literals;
			getPCSolver().setTrue(lits.literals[0], this);
		}
	} else {
		auto c = getPCSolver().createClause(lits, true);
		getPCSolver().addLearnedClause(c);

		//if unit propagation is already possible, this might not be detected on time, so help a little
		//MEANING: if lits is already completely false, this clause cannot be added to the store
		int unknown = 0;
		int unknindex = -1;
		bool allfalse = true;
		for (uint i = 0; unknown < 2 && i < lits.literals.size(); ++i) {
			if (value(lits.literals[i]) == l_Undef) {
				++unknown;
				unknindex = i;
				allfalse = false;
			} else if (value(lits.literals[i]) == l_True) {
				allfalse = false;
			}
		}
		if (allfalse) {
			return;
		}

		if (unknown == 1) {
			getPCSolver().setTrue(lits.literals[unknindex], this, c);
		}

		if (verbosity() >= 2) {
			clog << "Adding loop formula: [ ";
			MinisatID::toString(c, getPCSolver());
			clog << "].\n";
		}
	}

	MAssert(!isUnknown(l));
}

rClause IDSolver::getExplanation(const Lit& l) {
	MAssert(getPCSolver().modes().idclausesaving>0);
	Disjunction clause(reason(var(l)));
	return getPCSolver().createClause(clause, true);
}

/* Precondition:  seen(i)==0 for each i.
 * Postcondition: seen(i)  for exactly those i that are ancestors of cs in sp_justification. If modes.defn_search==stop_at_cs, there should not be other cycle sources then cs in the path from added literals to cs.
 */
void IDSolver::markNonJustified(Atom cs, varlist& tmpseen) {
	queue<Atom> q;
	markNonJustifiedAddParents(cs, cs, q, tmpseen);
	// Now recursively do the same with each enqueued Var.
	Atom x;
	while (q.size() > 0) {
		x = q.front();
		q.pop();
		markNonJustifiedAddParents(x, cs, q, tmpseen);
	}
}

void IDSolver::markNonJustifiedAddParents(Atom x, Atom cs, queue<Atom> &q, varlist& tmpseen) {
	Lit poslit = mkPosLit(x);
	const varlist& v = disj.occurs(poslit);
	for (auto i = v.cbegin(); i < v.cend(); ++i) {
		if (isDefInPosGraph(*i) && var(justification(*i)[0]) == x) {
			markNonJustifiedAddVar(*i, cs, q, tmpseen);
		}
	}
	const varlist& w = conj.occurs(poslit);
	for (auto i = w.cbegin(); i < w.cend(); ++i) {
		markNonJustifiedAddVar(*i, cs, q, tmpseen);
	}
	varlist heads = getDefAggHeadsWithBodyLit(x);
	for (varlist::size_type i = 0; i < heads.size(); ++i) {
		litlist& jstfc = justification(heads[i]);
		for (uint k = 0; k < jstfc.size(); ++k) {
			if (jstfc[k] == poslit) { // Found that x is actually used in y's justification.
				markNonJustifiedAddVar(heads[i], cs, q, tmpseen);
				break;
			}
		}
	}
}

inline void IDSolver::markNonJustifiedAddVar(Atom v, Atom cs, queue<Atom> &q, varlist& tmpseen) {
	// TODO prove whether this false can be here?
	if (/*!isFalse(v) && */inSameSCC(v, cs) && (getPCSolver().modes().defn_search == include_cs || v == cs || !isCS(v))) {
		if (seen(v) == 0) {
			seen(v) = 1;
			tmpseen.push_back(v);
			q.push(v);
			++stats.total_marked_size;
		} else {
			++seen(v);
		}

		if (verbosity() > 9) {
			clog << "Not justified " << toString(v) << ", times " << seen(v) << "\n";
		}
	}
}

void IDSolver::printPosGraphJustifications() const {
	clog << ">>>> Justifications (on pos graph):\n";
	for (auto i = defdVars.cbegin(); i < defdVars.cend(); ++i) {
		auto var = *i;
		if (isDefined(var) && occ(var) != MIXEDLOOP) {
			clog << "    " << toString(mkPosLit(var)) << "<-";
			switch (type(var)) {
			case DefType::DISJ:
				clog << toString(justification(var)[0]) << "; \n";
				break;
			case DefType::CONJ:
				clog << "all (conj) \n";
				break;
			case DefType::AGGR: {
				bool begin = true;
				for (auto j = justification(var).cbegin(); j < justification(var).cend(); ++j) {
					if (not begin) {
						clog << " ";
					}
					begin = false;
					clog << toString(*j);
				}
				clog << "\n";
				break;
			}
			}
		}
	}
	clog << "\n";
}

/**
 * Checks if there are any positive loops in the current depenndecy graph. Mainly used for debugging purposes (does slow bottom-up reasoning)
 * @precondition: propagation has to be at fixpoint! So is not necessarily correct at the end of finishparsing or notifypropagate!
 */
bool IDSolver::isCycleFree() const {
	if (!modes().checkcyclefreeness) {
		return true;
	}
#ifdef DEBUG
	for (int i = 0; i < nbvars; ++i) {
		MAssert(!isDefined(i) || justification(i).size()>0 || type(i)!=DefType::DISJ || occ(i)==MIXEDLOOP);
	}
#endif

	if (verbosity() >= 2) {
		printPosGraphJustifications();
	}

	// Verify cycles.
	varlist isfree(nbvars, 0); // per variable. 0 = free, >0 = number of literals in body still to be justified.
	queue<Lit> justified;
	uint cnt_nonjustified = 0;
	for (int i = 0; i < nbvars; ++i) {
		justified.push(mkLit(i, true)); // negative literals are justified anyhow.
		if (!isDefInPosGraph(i) || type(i) == DefType::AGGR) { // FIXME: ignores aggregates!
			justified.push(mkLit(i, false));
		} else {
			if (not isFalse(mkPosLit(i))) {
				//clog <<"Not justified " <<getPrintableVar(i) <<"\n";
				++cnt_nonjustified;
				isfree[i] = type(i) == DefType::CONJ ? definition(i)->size() : 1;
			}
		}
	}

	if (cnt_nonjustified == 0) {
		return true;
	}

	while (cnt_nonjustified > 0 && not justified.empty()) {
		auto l = justified.front();
		justified.pop();

		if (nbvars <= var(l)) {
			continue;
		}

		for (auto i = disj.occurs(l).cbegin(); i < disj.occurs(l).cend(); ++i) {
			Atom d = *i;
			MAssert(type(d)==DefType::DISJ && (!isDefInPosGraph(*i) || justification(d).size()==1));
			if (isfree[d] > 0 && justification(d)[0] == l) {
				MAssert(isfree[d]==1);
				isfree[d] = 0;
				justified.push(mkLit(d, false));
				--cnt_nonjustified;
				//clog <<"Justified " <<getPrintableVar(d) <<"\n";
			}
		}

		for (auto i = conj.occurs(l).cbegin(); i < conj.occurs(l).cend(); ++i) {
			Atom c = *i;
			MAssert(type(c)==DefType::CONJ);
			if (isfree[c] > 0) {
				isfree[c]--;
				if (isfree[c] == 0) {
					justified.push(mkLit(c, false));
					--cnt_nonjustified;
					//clog <<"Justified " <<getPrintableVar(c) <<"\n";
				}
			}
		}

		varlist as = getDefAggHeadsWithBodyLit(var(l));
		for (uint i = 0; i < as.size(); ++i) {
			Atom d = as[i];
			bool found = false;
			for (uint j = 0; j < justification(d).size(); ++j) {
				if (justification(d)[j] == l && isfree[d] > 0) {
					found = true;
					break;
				}
			}
			if (found) {
				isfree[d]--;
				if (isfree[d] == 0) {
					justified.push(mkLit(d, false));
					--cnt_nonjustified;
					//clog <<"Justified " <<getPrintableVar(d) <<"\n";
				}
			}
		}
	}

	if (cnt_nonjustified == 0) {
		if (verbosity() > 2) {
			clog << "OK, the justification is cycle free.\n";
		}
	} else {
		if (verbosity() > 2) {
			clog << "WARNING: " << cnt_nonjustified << " literals remain not-justified.\n";
		}
	}
	return cnt_nonjustified == 0;
}

/****************************
 * WELL FOUNDED MODEL CHECK *
 ****************************/

/**
 * ALGORITHM
 * The point is to calculate both an underapproximation and an overapproximation regarding the negative defined body literals, by
 * using for each iterating the derivation of the rule heads until the least fixpoint.
 * This boils down to two steps: in the first step, assuming all positive and all negative defined body literals are false and starting
 * derivation from there. Each time a head can be derived (in the underderivation, so certainly true), its body occurences can be updated.
 * When fixpoint is reached, then all negative defined body literals are made true (unless already derived), and in the same way an over
 * approximation is calculated (the positive body literals are still false). Everything that is derived there can still become true. So
 * all heads that are not derived after step two are certainly false. These steps are then iterated until complete fixpoint.
 * Optimisation 1: mark all literals that still have to be derived, avoiding to rederive them each iteration.
 * Optimisation 2: use counters indicating how many more elements have to become defined to be able to derive the head.
 *
 * Everything that is not derived in the end is unknown in the three-valued well-founded model, meaning that there is no two-valued well-
 * founded model, so the current interpretation is not a valid well-founded model.
 */
/**
 * TODO currently no well founded model checking over aggregates
 * this can be done by implementing wf propagation and counter methods in aggregates.
 */
bool printednontotalwarning = false;

#define DEFINEDINMIXED(v) (isDefined(v) && (occ(v) == DefOcc::BOTHLOOP || occ(v) == DefOcc::MIXEDLOOP))

rClause IDSolver::isWellFoundedModel() {
	MAssert(twovalueddef);

	if (getSemantics() != DEF_WELLF) {
		throw idpexception("Should not be checking for well-founded model, because mode is stable semantics!\n");
	}

#ifdef DEBUG
	if (posloops && !isCycleFree()) {
		if (verbosity() > 1) {
			clog <<"A positive unfounded loop exists, so not well-founded!\n";
		}
		return nullPtrClause;
	}
#endif

	if (!negloops) {
		if (verbosity() > 1) {
			clog << "Well-founded for positive loops, no negative loops present!\n";
		}
		return nullPtrClause;
	}

	if (mixedrecagg) {
		throw notYetImplemented("Checking wellfoundedness for recursively defined aggregates.\n");
	}

	// Initialize scc of full dependency graph
	//TODO also here use reduce memory overhead by only using it for defined variables!
	wfroot.clear();
	wfrootnodes.clear();
	wfqueue = queue<Lit>();
	wfmarkedAtoms.clear();
	wfisMarked.clear();
	wfroot.resize(nbvars, -1);
	varlist rootofmixed;
	wfisMarked.resize(nbvars, false);

	findMixedCycles(wfroot, rootofmixed);

	if (verbosity() > 1) {
		clog << "General SCCs: ";
		for (uint z = 0; z < wfroot.size(); ++z) {
			if (DEFINEDINMIXED(wfroot[z])) {
				clog << toString(z) << " has root " << toString(wfroot[z]) << "\n";
			}
		}
		clog << "\nMixed cycles are " << (rootofmixed.empty() ? "not" : "possibly") << " present.\n";
	}

	if (rootofmixed.empty()) {
		if (verbosity() > 1) {
			clog << "The model is well-founded!\n";
		} CHECKSEEN;
		return nullPtrClause;
	}

	markUpward();

	/**
	 * until full fixpoint
	 * 	pas de TP operator toe tot fixpoint
	 * 	hou een ondergrens en een bovengrens bij, voor de certainly true en de certainly false
	 * 	maak een gepaste onderschatting voor de negative unknown literals
	 * 	wat dan wordt afgeleid is certainly true
	 * 	maak een overschatting voor de negatieve unknown literals
	 * 	wat niet wordt afgeleid is certainly false
	 * 	kijk of full fixpoint reached, anders begin opnieuw
	 */
	wffixpoint = false;
	bool wellfounded = false;
	while (!wffixpoint && not wellfounded) {
		wffixpoint = true;

		initializeCounters();
		forwardPropagate(true);
		if (wfmarkedAtoms.empty()) {
			wellfounded = true;
		}
		overestimateCounters();
		forwardPropagate(false);
		removeMarks();
		if (wfmarkedAtoms.empty()) {
			wellfounded = true;
		}
	}

	for (int i = 0; i < nbvars; ++i) {
		seen(i) = 0;
	}

	if (wellfounded) {
		if (verbosity() > 1) {
			clog << "The model is well-founded!\n";
		} CHECKSEEN;
		return nullPtrClause;
	}

	if (verbosity() > 0 && not printednontotalwarning) {
		printednontotalwarning = true;
		clog << "The definition is not total (found an interpretation of the open symbols with a three-valued well-founded model).\n";
	}
	if (verbosity() > 1) {
		clog << "The model is not well-founded!\n";
	}

	//Returns the found assignment (TODO might be optimized to just return the loop)
	Disjunction invalidation({ });
	getPCSolver().invalidate(invalidation.literals);
	auto confl = getPCSolver().createClause(invalidation, true);
	getPCSolver().addConflictClause(confl);

	CHECKSEEN;

	return confl;
}

/**
 * Visit the heads of all rules and check the current JUSTIFICATION graph for loops with mixed signs
 * (because of standard propagation, there are no other loops). The head is always positive,
 * so pure negative loops are not possible.
 */
void IDSolver::findMixedCycles(varlist &root, vector<int>& rootofmixed) {
	vector<bool> incomp(nbvars, false);
	stack<Atom> stack;
	vector<int> visited(nbvars, 0); // =0 represents not visited; >0 corresponds to visited through a positive body literal, <0 through a negative body literal
	int counter = 1;

	for (auto i = defdVars.cbegin(); i < defdVars.cend(); ++i) {
		Atom v = *i;
		if (visited[v] == 0) {
			visitWF(v, root, incomp, stack, visited, counter, true, rootofmixed);
		}
	}
}

void IDSolver::visitWF(Atom v, varlist &root, vector<bool> &incomp, stack<Atom> &stack, varlist &visited, int& counter, bool throughPositiveLit,
		vector<int>& rootofmixed) {
	MAssert(!incomp[v]);
	MAssert(isDefined(v));
	if (not DEFINEDINMIXED(v)) {
		return;
	}
	MAssert(getDefVar(v)->type()!=DefType::AGGR);
	++counter;
	visited[v] = throughPositiveLit ? counter : -counter;
	root[v] = v;
	stack.push(v);

	bool headtrue = isTrue(mkPosLit(v));

	if (type(v) == DefType::AGGR) {
		/*litlist lits;
		 aggsolver->getLiteralsOfAggr(v, lits);
		 for(int i=0; i<lits.size(); ++i){
		 Lit l = lits[i];
		 Var w = var(l);
		 if(!isDefined(w)){
		 continue;
		 }
		 if(visited[w]==0){
		 visitWF(w, root, incomp, stack, visited, counter, isPositive(l), rootofmixed);
		 }else if(!incomp[w] && !isPositive(l) && visited[v]>0){
		 visited[v] = -visited[v];
		 }
		 if (!incomp[w] && abs(visited[root[v]])>abs(visited[root[w]])){
		 root[v] = root[w];
		 }
		 }*/
	} else if ((headtrue && isConjunctive(v)) || (!headtrue && isDisjunctive(v))) {
		//head is false and disj, or head is true and conj: all body literals are its justification
		for (uint i = 0; i < definition(v)->size(); ++i) {
			Lit l = definition(v)->operator [](i);
			Atom w = var(l);
			if (not DEFINEDINMIXED(w)) {
				continue;
			}
			if (visited[w] == 0) {
				visitWF(w, root, incomp, stack, visited, counter, isPositive(l), rootofmixed);
			} else if (!incomp[w] && !isPositive(l) && visited[v] > 0) {
				visited[v] = -visited[v];
			}
			if (!incomp[w] && abs(visited[root[v]]) > abs(visited[root[w]])) {
				root[v] = root[w];
			}
		}
	} else { //head is true and DefType::DISJ or head is false and DefType::CONJ: one literal is needed for justification
		// for DefType::DISJ, the justification is already known TODO INCORRECT when no pos loops possible over head!
		// for a DefType::CONJ, randomly choose one of the false body literals. If there is no loop through it, then it is a good choice.
		//			If there is, it will be found later if another false literal exists without a mixed loop.
		Lit l = mkLit(getMaxElem<int>());
		bool found = false;
		if (isConjunctive(v)) {
			for (uint i = 0; i < definition(v)->size(); ++i) {
				Lit l2 = definition(v)->operator [](i);
				if (isFalse(l2)) {
					l = l2;
					found = true;
					break;
				}
			}
		} else {
			for (uint i = 0; i < definition(v)->size(); ++i) {
				Lit l2 = definition(v)->operator [](i);
				if (isTrue(l2)) {
					l = l2;
					found = true;
					break;
				}
			}
		}
		MAssert(found);
		MAssert(var(l)>-1);
		Atom w = var(l);
		if (DEFINEDINMIXED(w)) {
			if (visited[w] == 0) {
				visitWF(w, root, incomp, stack, visited, counter, isPositive(l), rootofmixed);
			} else if (!incomp[w] && !isPositive(l) && visited[v] > 0) {
				visited[v] = -visited[v];
			}
			if (!incomp[w] && abs(visited[root[v]]) > abs(visited[root[w]])) {
				root[v] = root[w];
			}
		}
	}
	if (root[v] == v) {
		wfrootnodes.push_back(v);
		bool mixed = false;
		int w;
		do {
			w = stack.top();
			stack.pop();
			visited[w] < 0 ? mixed = true : true;
			root[w] = v; //these are the found sccs
			incomp[w] = true;
		} while (w != v);
		if (mixed) {
			rootofmixed.push_back(v);
		}
	}
}

/**
 * De markering geeft aan welke atomen nog UNKNOWN zijn, dus in de huidige iteratie nog niet konden worden
 * afgeleid door de lower en upper bounds.
 *
 * Hoe de initiele bepalen: de cycle source is unknown. Alle heads die daarvan afhangen omdat het in de justification zit zijn unknown
 *
 * Dus vanaf nu markering voor VARS niet voor literals
 */

/**
 * Marks the head of a rule
 */
void IDSolver::mark(Atom h) {
	Lit l = mkLit(h, isFalse(mkPosLit(h))); //holds the literal that has to be propagated, so has the model value
	if (!wfisMarked[h] && getDefVar(h)->type() != DefType::AGGR) { //FIXME: initializecounters cannot handle aggregates, but at this moment we know they will not be recursive!
		wfqueue.push(l);
		wfisMarked[h] = true;
		//clog <<"Marked " <<toString(h) <<"\n";
		wfmarkedAtoms.insert(h);
	}
}

/**
 * marks all literals that can be reached upwards from the cycle roots.
 */
void IDSolver::markUpward() {
	for (varlist::size_type n = 0; n < wfrootnodes.size(); ++n) {
		Atom temp = wfrootnodes[n];
		mark(temp);
	}

	while (!wfqueue.empty()) {
		Lit l = wfqueue.front();
		wfqueue.pop();

		for (auto l2 : conj.occurs(l)) {
			mark(l2);
		}
		for (auto l2 : disj.occurs(l)) {
			mark(l2);
		}

		l = not l;

		for (auto l2 : conj.occurs(l)) {
			mark(l2);
		}
		for (auto l2 : disj.occurs(l)) {
			mark(l2);
		}

		/*TODO? if(aggsolver!=NULL){
		 litlist heads;
		 aggsolver->getHeadsOfAggrInWhichOccurs(var(l), heads);
		 for(int i=0; i<heads.size(); ++i){
		 mark(heads[i]);
		 }
		 }*/
	}
}

/**
 * Initializes the body counter of the rules on the number of marked body literals.
 * If there are no unmarked literals (counter==0) or the value can be derived directly from only one atom (disj and true, conj and false)
 * the head is pushed on the propagation q.
 *
 * The DefType::CONJ counters count the number of literals still needed to make the DefType::CONJ true
 * The DefType::DISJ counters count the number of literals still needed to make the DefType::DISJ false
 */
void IDSolver::initializeCounters() {
	for (auto i = wfmarkedAtoms.cbegin(); i != wfmarkedAtoms.cend(); ++i) {
		Atom v = *i;
		seen(v) = 0;
		bool canbepropagated = false;
		for (uint j = 0; !canbepropagated && j < definition(v)->size(); ++j) {
			Lit bl = definition(v)->operator [](j);
			if (wfisMarked[var(bl)]) {
				++seen(v);
			} else if (isFalse(bl) && type(v) == DefType::CONJ) {
				canbepropagated = true;
			} else if (isTrue(bl) && type(v) == DefType::DISJ && var(bl) != v) {
				canbepropagated = true;
			}
		}
		if (seen(v) == 0 || canbepropagated) {
			seen(v) = 0;
			wfqueue.push(isTrue(mkPosLit(v)) ? mkPosLit(v) : mkNegLit(v));
		}
	}
}

/*
 * marked geeft aan dat een atoom in de huidige iteratie nog unknown is. En de counter geven aan hoeveel er
 * nog nodig zijn om de head respectievelijk true (conj) of false (disj) te maken
 * Maar de rest moet nog omgeschreven worden in deze vorm.
 *
 * De propagate queue is dan een queue die bijhoudt of iets een waarde heeft gekregen (de waarde van het model dan) en dat dat gepropageerd
 * moet worden
 */

/**
 * Counters probably keep the number of literals needed to make it true for DefType::CONJ and the number of literals needed to make it false for DefType::DISJ!!!
 */
void IDSolver::forwardPropagate(bool removemarks) {
	while (!wfqueue.empty()) {
		Lit l = wfqueue.front();
		wfqueue.pop();

		if (!wfisMarked[var(l)]) {
			continue;
		}
		wfisMarked[var(l)] = false;

		//clog <<"Forward propagate of " <<toString(var(l)) <<"\n";

		if (removemarks) {
			//clog <<"Unmarked " <<toString(var(l)) <<"\n";
			wfmarkedAtoms.erase(var(l));
			wffixpoint = false;
		}

		//Literal l has become true, so for all rules with body literal l and marked head,
		//if DefType::DISJ, then head will be true, so add true head to queue and set counter to 0
		for (auto i = disj.occurs(l).cbegin(); i < disj.occurs(l).cend(); ++i) {
			Atom head = *i;
			if (wfisMarked[head]) {
				wfqueue.push(mkPosLit(head));
				seen(head) = 0;
			}
		}

		//if DefType::CONJ and counter gets 0, then head will be true, so add true head to queue
		for (auto i = conj.occurs(l).cbegin(); i < conj.occurs(l).cend(); ++i) {
			Atom head = *i;
			if (wfisMarked[head] && --seen(head) == 0) {
				wfqueue.push(mkPosLit(head));
			}
		}

		l = not l;

		//Literal l has become false, so for all rules with body literal l and marked head,
		//if DefType::DISJ and counter gets 0, then head will be false, so add false head to queue
		for (auto i = disj.occurs(l).cbegin(); i < disj.occurs(l).cend(); ++i) {
			Atom head = *i;
			if (wfisMarked[head] && --seen(head) == 0) {
				wfqueue.push(mkNegLit(head));
			}
		}

		//if DefType::CONJ, then head will be false, so add false head to queue and set counter to 0
		for (auto i = conj.occurs(l).cbegin(); i < conj.occurs(l).cend(); ++i) {
			Atom head = *i;
			if (wfisMarked[head]) {
				wfqueue.push(mkNegLit(head));
				seen(head) = 0;
			}
		}

		//TODO DefType::AGGREGATES
	}
}

/**
 * Overestimate the counters by making all negative defined marked body literals true.
 */
void IDSolver::overestimateCounters() {
	for (set<Atom>::iterator i = wfmarkedAtoms.cbegin(); i != wfmarkedAtoms.cend(); ++i) {
		Atom v = *i;
		MAssert(seen(v) > 0);

		//clog <<"For marked lit " <<toString(v) <<"\n";

		for (uint j = 0; j < definition(v)->size(); ++j) {
			const Lit& bdl = definition(v)->operator [](j);
			if (wfisMarked[var(bdl)] && !isPositive(bdl) && v != var(bdl)) {
				//clog <<"bdl " <<toString(bdl) <<" can be made true \n";
				if (type(v) == DefType::CONJ) {
					seen(v)--;}
				else {
					seen(v) = 0;
				}
			}
		}

		if (seen(v) == 0) {
			//clog <<"So could be pushed.\n";
			wfqueue.push(mkPosLit(v));
		}
	}
}

/**
 * Removes all elements from the marked stack that are still marked. These have not been derived, so are certainly false.
 * All those that are still on the marked stack, but are not longer marked, are still undefined after this iteration, so
 * are marked again.
 */
void IDSolver::removeMarks() {
	stack<Atom> temp;
	for (set<Atom>::iterator i = wfmarkedAtoms.cbegin(); i != wfmarkedAtoms.cend(); ++i) {
		Atom v = *i;
		if (wfisMarked[v]) {
			temp.push(v);
			wfisMarked[v] = false;
			wffixpoint = false;
		} else {
			wfisMarked[v] = true;
		}
	}
	while (!temp.empty()) {
		//clog <<"Unmarked " <<toString(temp.top()) <<"\n";
		wfmarkedAtoms.erase(temp.top());
		temp.pop();
	}
}

// PRINT INFORMATION

void IDSolver::printRule(Atom var) const {
	MAssert(isDefined(var));
	if (isDisjunctive(var)) {
		clog << toString(var) << " <- ";
		bool begin = true;
		for (auto b : definition(var)->getBody()) {
			if (not begin) {
				clog << " | ";
			}
			begin = false;
			clog << toString(b);
		}
		clog << "\n";
	} else if (isConjunctive(var)) {
		clog << toString(var) << " <- ";
		bool begin = true;
		for (auto b : definition(var)->getBody()) {
			if (not begin) {
				clog << " & ";
			}
			begin = false;
			clog << toString(b);
		}
		clog << "\n";
	} else {
		MAssert(isDefinedByAggr(var));
		// TODO
	}
}

AggProp const * getProp(AggType type) {
	switch (type) {
	case AggType::MAX:
		return AggProp::getMax();
	case AggType::SUM:
		return AggProp::getSum();
	case AggType::PROD:
		return AggProp::getProd();
	case AggType::CARD:
		return AggProp::getCard();
	default:
		MAssert(false);
		return NULL;
	}
}

bool IDSolver::canJustifyHead(const IDAgg& agg, litlist& jstf, varlist& nonjstf, const InterMediateDataStruct& currentjust, bool real) const {
	if (agg.getType() == AggType::MAX) {
		return canJustifyMaxHead(agg, jstf, nonjstf, currentjust, real);
	} else {
		MAssert(agg.getType()==AggType::PROD || agg.getType()==AggType::SUM || agg.getType()==AggType::CARD);
		return canJustifySPHead(agg, jstf, nonjstf, currentjust, real);
	}
}

bool IDSolver::canJustifyMaxHead(const IDAgg& agg, litlist& jstf, varlist& nonjstf, const InterMediateDataStruct& currentjust, bool real) const {
	auto wl = agg.getWL();

	bool justified;
	if (agg.hasUB()) {
		justified = false;
		for (auto i = wl.crbegin(); i < wl.crend() && i->getWeight() > agg.getBound(); ++i) {
			if (oppositeIsJustified(currentjust, *i, real)) {
				jstf.push_back(not i->getLit()); //push negative literal, because it should become false
			} else if (real || currentjust.getElem(var(i->getLit())) != 0) {
				nonjstf.push_back(var(i->getLit()));
			}
		}
		if (nonjstf.size() == 0) {
			justified = true;
		}
	} else { // LB
		justified = false;
		for (auto i = wl.crbegin(); i < wl.crend() && i->getWeight() >= agg.getBound(); ++i) {
			if (isJustified(currentjust, *i, real)) {
				jstf.push_back(i->getLit());
				justified = true;
			} else if (real || (currentjust.hasElem(var(i->getLit())) && currentjust.getElem(var(i->getLit())) != 0)) {
				nonjstf.push_back(var(i->getLit()));
			}
		}
	}

	if (not justified) {
		jstf.clear();
	}
	return justified;
}

/**
 * AGG <= B: v is justified if one literal below/eq the bound is THAT IS NOT THE HEAD
 * 					if so, change the justification to the literal
 * 					otherwise, add all nonfalse, non-justified, relevant, below the bound literals to the queue
 * A <= AGG: v is justified if the negation of all literals below the bound are. The emptyset is always a solution,
 * 			 so no conclusions have to be drawn from the literals above/eq the bound
 * 					if so, change the justification to the negation of all those below the bound literals
 * 					otherwise, add all nonfalse, non-justified, relevant, below the bound literals to the queue
 */
bool IDSolver::canJustifySPHead(const IDAgg& agg, litlist& jstf, varlist& nonjstf, const InterMediateDataStruct& currentjust, bool real) const {
	const AggProp & type = *getProp(agg.getType());
	bool justified = true;
	auto wl = agg.getWL();

	if (justified && agg.hasUB()) {
		justified = false;
		auto bestpossible = type.getMaxPossible(wl);
		for (vwl::const_iterator i = wl.cbegin(); !justified && i < wl.cend(); ++i) {
			if (oppositeIsJustified(currentjust, *i, real)) {
				jstf.push_back(not i->getLit());
				bestpossible = type.removeMax(bestpossible, i->getWeight());
				if (bestpossible <= agg.getBound()) {
					justified = true;
				}
			} else if (real || currentjust.getElem(var(i->getLit())) != 0) {
				nonjstf.push_back(var(i->getLit()));
			}
		}
	}
	if (justified && agg.hasLB()) {
		justified = false;
		auto bestcertain = type.getMinPossible(wl);
		for (vwl::const_iterator i = wl.cbegin(); !justified && i < wl.cend(); ++i) {
			if (isJustified(currentjust, *i, real)) {
				jstf.push_back(i->getLit());
				bestcertain = type.add(bestcertain, i->getWeight());
				if (bestcertain >= agg.getBound()) {
					justified = true;
				}
			} else if (real || (currentjust.hasElem(var(i->getLit())) && currentjust.getElem(var(i->getLit())) != 0)) {
				nonjstf.push_back(var(i->getLit()));
			}
		}
	}

	if (!justified) {
		jstf.clear();
	}

	return justified;
}

IDAgg* IDSolver::getAggDefiningHead(Atom v) const {
	return aggdefinition(v);
}

varlist IDSolver::getDefAggHeadsWithBodyLit(Atom x) const {
	varlist heads;
	for (auto i = aggr.occurs(mkPosLit(x)).cbegin(); i < aggr.occurs(mkPosLit(x)).cend(); ++i) {
		heads.push_back(*i);
	}
	for (auto i = aggr.occurs(mkNegLit(x)).cbegin(); i < aggr.occurs(mkNegLit(x)).cend(); ++i) {
		heads.push_back(*i);
	}
	return heads;
}

vwl::const_iterator IDSolver::getSetLitsOfAggWithHeadBegin(Atom x) const {
	return getAggDefiningHead(x)->getWL().cbegin();
}

vwl::const_iterator IDSolver::getSetLitsOfAggWithHeadEnd(Atom x) const {
	return getAggDefiningHead(x)->getWL().cend();
}

/**
 * For an aggregate expression defined by v, add all set literals to loopf that
 * 		- have not been added already(seen[A]==1 for A, seen[A]==2 for not A)
 * 		- might help to make the expression true (monotone literals!) (to make it a more relevant learned clause)
 * Currently CONSIDERABLE overapproximation: take all known false literals which are set literal or its negation,
 * do not occur in ufs and have not been seen yet.
 * Probably NEVER usable external clause!
 * TODO: optimize: add monotone literals until the aggregate can become true
 */
void IDSolver::addExternalLiterals(Atom v, const std::set<Atom>& ufs, litlist& loopf, InterMediateDataStruct& seen) {
	for (vwl::const_iterator i = getAggDefiningHead(v)->getWL().cbegin(); i < getAggDefiningHead(v)->getWL().cend(); ++i) {
		Lit l = i->getLit();
		if (ufs.find(var(l)) != ufs.cend() || seen.getElem(var(l)) == (isPositive(l) ? 2 : 1)) {
			continue;
		}

		if (isTrue(l)) {
			l = not l;
		}

		if (!isFalse(l)) {
			continue;
		}

		loopf.push_back(l);
		seen.getElem(var(l)) = isPositive(l) ? 2 : 1;
	}
}

/**
 * The given head is not false. So it has a (possibly looping) justification. Find this justification
 */
void IDSolver::findJustificationAggr(Atom head, litlist& outjstf) {
	varlist nonjstf;
	InterMediateDataStruct* currentjust = new InterMediateDataStruct(0, 0); //create an empty justification
	const IDAgg& agg = *getAggDefiningHead(head);
	canJustifyHead(agg, outjstf, nonjstf, *currentjust, true);
	delete currentjust;
}

/**
 * Check whether the given var is justified by the current justification graph. If this is the case, jstf will
 * contain its justification and true will be returned. Otherwise, false will be returned and nonjstf will contain
 * all body literals of v that are not justified.
 */
bool IDSolver::directlyJustifiable(Atom v, litlist& jstf, varlist& nonjstf, InterMediateDataStruct& currentjust) {
	const IDAgg& agg = *getAggDefiningHead(v);
	return canJustifyHead(agg, jstf, nonjstf, currentjust, false);
}

bool IDSolver::isInitiallyJustified(const IDAgg& agg) {
	if (agg.getSign() == AggSign::LB && getProp(agg.getType())->getMinPossible(agg.getWL()) >= agg.getBound()) {
		return true;
	} else if (agg.getSign() == AggSign::UB && getProp(agg.getType())->getMaxPossible(agg.getWL()) <= agg.getBound()) {
		return true;
	}
	return false;
}
