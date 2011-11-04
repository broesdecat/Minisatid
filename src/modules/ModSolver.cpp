/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#include "modules/ModSolver.hpp"

#include "utils/Utils.hpp"
#include "utils/Print.hpp"
#include <vector>
#include <algorithm>

#include "external/ExternalInterface.hpp"
#include "theorysolvers/PCSolver.hpp"
#include "theorysolvers/SOSolver.hpp"

#include "utils/Print.hpp"

using namespace std;
using namespace MinisatID;

//Important: The head variable does not occur in this theory, so should NOT automatically be
//added as a var in it.
/**
 * Constructs a ModSolver, with a given head, index and hierarchy pointer. A PCSolver is initialized.
 */
ModSolver::ModSolver(modindex child, Var head, SOSolver* mh):
		Propagator(new PCSolver(mh->modes(), *this, child)), WrapperPimpl(mh->modes(), mh->getParent().getRemapper()),
		init(false), hasparent(false), searching(false),
		head(head),
		id(child), parentid(-1), //, startedsearch(false), startindex(-1),
		modhier(mh){
	getPCSolver().setNbModels(1);
	//If we are not debugging, we do not want information on the deeper levels
	if(mh->modes().verbosity<2){
		getPCSolver().setVerbosity(0);
	}

	getPCSolver().setModSolver(this);

	trail.push_back(vector<Lit>());

	getPCSolver().accept(this, EV_PRINTSTATE);
	getPCSolver().accept(this, EV_DECISIONLEVEL);
	getPCSolver().accept(this, EV_BACKTRACK);
	getPCSolver().accept(this, EV_FULLASSIGNMENT);
	getPCSolver().acceptFinishParsing(this, true);
}

void ModSolver::addModel(const InnerModel& model){
	if(getNonConstModSolverData().isRoot(this)){
		getNonConstModSolverData().addModel(model);
	}
	int origverb = getModSolverData().modes().verbosity;
	if(origverb<2){
		WrapperPimpl::_modes.verbosity = 0;
	}
	WrapperPimpl::addModel(model);
	WrapperPimpl::_modes.verbosity = origverb;
}

ModSolver::~ModSolver(){
	delete pcsolver;
}

SATVAL ModSolver::add(Var var){
	if(getModSolverData().modes().verbosity>5){
		report("Var %d added to modal solver %zu.\n", getPrintableVar(var), getPrintId());
	}
	getPCSolver().add(var);
	registeredvars.push_back(var);
	return SATVAL::POS_SAT;
}

/**
 * Add all variables in the given vector as variables in the theory.
 */
void ModSolver::addVars(const litlist& a){
	for(auto i=a.cbegin(); i<a.cend(); ++i){
		add(var(*i));
	}
}

SATVAL ModSolver::add(const InnerDisjunction& disj){
	addVars(disj.literals);
	getPCSolver().add(disj);
	return getPCSolver().satState();
}

SATVAL ModSolver::add(const InnerRule& rule){
	add(rule.head);
	addVars(rule.body);
	getPCSolver().add(rule);
	return getPCSolver().satState();
}
SATVAL ModSolver::add(const InnerWLSet& set){
	for(auto i=set.wls.cbegin(); i!=set.wls.cend(); ++i){
		addVar((*i).getLit());
	}
	getPCSolver().add(set);
	return getPCSolver().satState();
}

SATVAL ModSolver::add(const InnerAggregate& agg){
	getPCSolver().add(agg);
	return getPCSolver().satState();
}

SATVAL ModSolver::add(const InnerReifAggregate& agg){
	add(agg.head);
	getPCSolver().add(agg);
	return getPCSolver().satState();
}

/**
 * Adds the list of variables to the rigid atoms of this ModSolver. They are automatically added
 * as variables, this is maybe not completely necessary when they are not used in the PC theory,
 * but requires some algorithmic changes then, so currently they are added. In addition,
 * they are added as variables to the parent solver, that has to decide on values for them.
 */
SATVAL ModSolver::add(const InnerRigidAtoms& rigid){
	for(vector<Var>::const_iterator i=rigid.rigidatoms.cbegin(); i<rigid.rigidatoms.cend(); ++i){
		atoms.push_back(*i);
		add(*i);
		getModSolverData().getModSolver(getParentId())->add(*i);
	}

	//Creates a bool-vector mapping each atom to whether it was propagated from above or from this theory
	propfromabove = vector<bool>(atoms.size(), false);
	return SATVAL::POS_SAT;
}


/**
 * Sets the id of the parent modal solver. All rigid atoms are then added (possibly again) to the
 * parent solver, as well as this solver as a child and the head as a variable.
 */
void ModSolver::setParent(modindex parentid){
	this->parentid = parentid; hasparent = true;
	ModSolver* parent = getModSolverData().getModSolver(getParentId());
	for(vector<Var>::const_iterator i=atoms.cbegin(); i<atoms.cend(); ++i){
		parent->add(*i);
	}
	parent->addChild(this->id);
	parent->add(head.atom);
}

SATVAL ModSolver::addChild(int childid){
	children.push_back(childid);
	return SATVAL::POS_SAT;
}

/**
 * Recursively notify all Solvers that parsing has finished
 */
void ModSolver::finishParsingDown(bool& unsat){
	notifyParsed();
	getPCSolver().finishParsing(unsat);

	for(auto i=registeredvars.cbegin(); i<registeredvars.cend(); ++i){
		getPCSolver().accept(this, mkLit(*i, true), SLOW);
		getPCSolver().accept(this, mkLit(*i, false), SLOW);
	}

	for(auto i=getChildren().cbegin(); !unsat && i<getChildren().cend(); ++i){
		bool childunsat = false;
		getModSolverData().getModSolver(*i)->finishParsingDown(childunsat);
		//TODO handle !present
		//TODO handle unsat => might make this solver !present
	}
	notifyInitialized();
}

/**
 * Tells the root solver to do model expansion on his theory
 */
bool ModSolver::solve(const litlist& assumptions, const ModelExpandOptions& options){
	ModelExpandOptions modoptions;
	modoptions.printmodels = PRINT_NONE;
	modoptions.savemodels = SAVE_NONE;
	modoptions.search = MODELEXPAND;
	modoptions.nbmodelstofind = options.nbmodelstofind;
	Solution* s = new Solution(modoptions);
	setSolutionMonitor(s);
	//TODO set resource manager to get output
	bool result = getPCSolver().solve(assumptions, modoptions);
	setSolutionMonitor(NULL);
	delete s;
	return result;
}

void ModSolver::notifyNewDecisionLevel(){
	trail.push_back(vector<Lit>());
}

void ModSolver::doUnitPropagation(const litlist& assumpts){

}

bool ModSolver::search(const litlist& assumpts, bool search){
	/*
	 * In the end, we would want to propagate level by level, without having to restart the whole process
	 * every time. This requires a startsearch and continuesearch procedure in the SAT-solver
	 * As this is rather tedious, we will delay it until necessary.
	bool result = true;
	if(startindex==-1){
		result = getPCSolver().startSearch();
		startindex = 0;
	}
	for(; result && startindex<assumptions.size(); ++startindex){
		result = getPCSolver().propagate(assumptions[startindex]);
	}
	if(search && result){
		searching = true;
		result = getPCSolver().continueSearch();
		searching = false;
	}

	return result;*/

	bool result;
	searching = search;
	ModelExpandOptions options;
	options.printmodels = PRINT_NONE;
	options.savemodels = SAVE_NONE;
	options.search = MODELEXPAND;
	options.nbmodelstofind = 1;
	Solution* s = new Solution(options);
	setSolutionMonitor(s);
	result = getPCSolver().solve(assumpts, options);
	setSolutionMonitor(NULL);
	delete s;
	searching = false;
	return result;
}

void ModSolver::finishParsing(bool& present, bool& unsat){
	init = true;
}

/**
 * Returns non-owning pointer
 */
rClause ModSolver::notifypropagate(){
	rClause confl = nullPtrClause;
	if(!searching){
		vector<Lit> v = getPCSolver().getDecisions();
		//TODO propagate up WITH reason
	}

	while(hasNextProp() && confl==nullPtrClause){
		const Lit& l = getNextProp();
		if(getModSolverData().modes().verbosity>4){
			clog <<">>Propagated " <<l <<" from PC in mod " <<getPrintId() <<".\n";
		}

		trail.back().push_back(l);
		for(vmodindex::const_iterator i=getChildren().cbegin(); confl==nullPtrClause && i<getChildren().cend(); ++i){
			confl = getModSolverData().getModSolver(*i)->propagateDown(l);
		}
	}

	if(confl!=nullPtrClause){
		return confl;
	}

	//In future, we might want to delay effectively propagating and searching in subfolders to the point where the
	//queue is empty, so we will need a propagateDown and a propagateDownEndOfQueue
	bool noconflict = true;
	InnerDisjunction confldisj;
	for(vmodindex::const_iterator i=getChildren().cbegin(); noconflict && i<getChildren().cend(); ++i){
		assert(confldisj.literals.size()==0);
		noconflict = getModSolverData().getModSolver(*i)->propagateDownAtEndOfQueue(confldisj.literals);
	}

	if(!noconflict){
		confl = getPCSolver().createClause(confldisj, true);
		getPCSolver().addLearnedClause(confl);

		if(getModSolverData().modes().verbosity>=5){
			print(confl, getPCSolver());
		}
	}
	return confl;
}

/**
 * Propagates l to be true from the parent modal solver.
 * As long as the PC-solver is still propagating, this solver should not do anything more than store
 * the propagation, as modal satisfiability checking can be much more expensive. So this solver always
 * return NULL (if not, it should return a non-owning pointer).
 */
rClause ModSolver::propagateDown(Lit l){
	if(getModSolverData().modes().verbosity>4){
		clog <<l <<" propagated down into modal solver " <<getPrintId() <<".\n";
	}

	adaptValuesOnPropagation(l);

	return nullPtrClause;
}

/**
 * Checks whether l is relevant to this modal theory (the head or a rigid atom).
 * If this is the case, it adapts the data structures.
 */
void ModSolver::adaptValuesOnPropagation(Lit l){
	//Adapt head value
	if(getHead()==var(l)){
		assert(getHeadValue()==l_Undef);
		head.value = !sign(l)?l_True:l_False;
	}

	//adapt rigid atoms value
	for(vector<AV>::size_type i=0; i<atoms.size(); ++i){
		if(var(l)==atoms[i]){
			propfromabove[i]=true;
			assumptions.push_back(l);
			break;
		}
	}
}

/**
 * Notifies the modal solver that propagation of the parent solver are finished. At this point, the modal solver
 * will be propagated.
 * Returns true if no conflict ensues
 */
bool ModSolver::propagateDownAtEndOfQueue(litlist& confldisj){
	if(!init){ return true; }
	if(getModSolverData().modes().verbosity>4){
		report("End of queue propagation down into modal solver %zu.\n", getPrintId());
	}

	bool allknown = false;

	/*TODO future:
	bool result;
	if(!allknown){
		result = doUnitPropagation(assumpts);
	}else{
		result = search(assumpts);
	}
	*/

	if((vsize)assumptions.size()==getAtoms().size() && (!hasparent || getHeadValue()!=l_Undef)){
		allknown = true;
	}

	getPCSolver().saveState(); //IMPORTANT
	bool result = search(assumptions, allknown);
	result = analyzeResult(result, allknown, confldisj);
	getPCSolver().resetState();

	if(getModSolverData().modes().verbosity>4){
		report("Finished checking solver %zu: %s.\n", getPrintId(), result?"no conflict":"conflict");
	}

	return result;
}

void ModSolver::notifyBacktrack(int untillevel, const Lit& decision){
	if(getModSolverData().modes().verbosity>4){
		report("Backtracking from PC in mod %zu to level %d\n", getPrintId(), untillevel);
	}

	while(trail.size()>((vsize)(untillevel+1))){
		//IMPORTANT: backtrack in REVERSE trail order! from latest to earliest!
		for(vector<Lit>::const_reverse_iterator i=trail.back().rbegin(); i<trail.back().rend(); ++i){
			for(vmodindex::const_iterator j=getChildren().cbegin(); j<getChildren().cend(); ++j){
				getModSolverData().getModSolver((*j))->backtrackFromAbove(*i);
			}
		}
		trail.pop_back();
	}

	Propagator::notifyBacktrack(untillevel, decision);
}

/**
 * For backtracking on rigid atoms, there are two possibilities:
 * 		the backtracking comes from above, so it has to be done
 * 		the backtracking is from the PC-solver
 * 			in this case, it might be that it was propagated or chosen by the PC Solver, in which case it should be backtracked
 * 						or it might be that it was propagated from above, in which case it should NOT be backtracked
 * 			currently, this is solved by storing an boolean remembering whether it was propagated from above or from the pc solver
 */
void ModSolver::backtrackFromAbove(Lit l){
	if(getModSolverData().modes().verbosity>4){
		clog <<"Backtracking " <<l <<" from above in mod " <<getPrintId() <<"\n";
	}

	if(var(l)==getHead() && getHeadValue()!=l_Undef){
		head.value = l_Undef;
	}
	for(vector<AV>::size_type i=0; i<atoms.size(); ++i){
		if(atoms[i]==var(l)){
			if(propfromabove[i] && var(l)==var(assumptions.back())){
				assumptions.pop_back();
				//startindex--;
				int solverlevel = getPCSolver().getLevel(var(l));
				if(solverlevel>=0){ //otherwise it was not propagated!
					getPCSolver().backtrackTo(solverlevel);
				}
				propfromabove[i] = false;
				break;
			}else{
#ifndef NDEBUG
				for(int j=0; j<assumptions.size(); ++j){
					assert(var(assumptions[j])!=var(l));
				}
#endif
			}
		}
	}
}

/**
 * Important, returns a clause constructed to be added to the PARENT solver: the vars are NOT necessarily
 * decision vars in this PC solver
 * Returns true if no conflict ensues
 */
bool ModSolver::analyzeResult(bool result, bool allknown, litlist& confldisj){
	bool conflict = false;
	//if no model found and should be sat or if model found, should be unsat and all values are known
	if(getHeadValue()==l_True && !result){
		conflict = true;
	}
	if(getHeadValue()==l_False && result && allknown){
		conflict = true;
	}

	if(conflict){ //conflict between head and body
		//TODO can the clause learning be improved?
		assert(confldisj.size()==0);
		if(getHeadValue()!=l_Undef){
			confldisj.push_back(mkLit(getHead(), getHeadValue()==l_True));
		}
		//TODO order of lits in conflict depends on order of assumptions and on order of propagations by parent
		for(int i=0; i<assumptions.size(); ++i){
			if(propfromabove[i]){
				confldisj.push_back(~assumptions[i]);
			}
		}
		assert(confldisj.size()>0);
	}

	return !conflict;
}

void ModSolver::printState() const{
	print(this);
}

void ModSolver::printModel(){
	//TODO implement
	//getPCSolver().printModel();
}
