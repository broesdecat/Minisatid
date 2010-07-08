#include "solvers/ModSolver.hpp"
#include "solvers/Utils.hpp"
#include <algorithm>

//Important: The head variable does not occur in this theory, so should NOT automatically be
//added as a var in it.
/**
 * Constructs a ModSolver, with a given head, index and hierarchy pointer. A PCSolver is initialized.
 */
ModSolver::ModSolver(modindex child, Var head, shared_ptr<ModSolverData> mh):
		id(child), parentid(-1), hasparent(false), init(true), //, startedsearch(false), startindex(-1),
		head(head), modhier(mh){
	ECNF_mode modescopy(mh->modes());
	modescopy.nbmodels = 1;

	solver = new PCSolver(modescopy);
	getSolver()->setModSolver(this);
}

ModSolver::~ModSolver(){
	delete solver;
}

/******************************
 * ADD/INITIALIZATION METHODS *
 ******************************/

void ModSolver::addVar(Var var){
	if(modhier.lock()->modes().verbosity>5){
		reportf("Var %d added to modal solver %zu.\n", var, getPrintId());
	}
	getSolver()->addVar(var);
}

/**
 * Add all variables in the given vector as variables in the theory.
 */
void ModSolver::addVars(vec<Lit>& a){
	for(int i=0; i<a.size(); i++){
		addVar(var(a[i]));
	}
}

bool ModSolver::addClause(vec<Lit>& lits){
	addVars(lits);
	return getSolver()->addClause(lits);
}

bool ModSolver::addRule(bool conj, vec<Lit>& lits){
	addVars(lits);
	return getSolver()->addRule(conj,lits);
}

bool ModSolver::addSet(int setid, vec<Lit>& lits, vector<Weight>& w){
	addVars(lits);
	return getSolver()->addSet(setid, lits, w);
}

bool ModSolver::addAggrExpr(Lit head, int set_id, Weight bound, bool lower, AggrType type, bool defined){
	addVar(var(head));
	return getSolver()->addAggrExpr(head, set_id, bound, lower, type, defined);
}

void ModSolver::setNbModels(int nb){
	getSolver()->setNbModels(nb);
}

void ModSolver::setRes(FILE* f){
	getSolver()->setRes(f);
}

/**
 * Adds the list of variables to the rigid atoms of this ModSolver. They are automatically added
 * as variables, this is maybe not completely necessary when they are not used in the PC theory,
 * but requires some algorithmic changes then, so currently they are added. In addition,
 * they are added as variables to the parent solver, that has to decide on values for them.
 */
void ModSolver::addAtoms(const vector<Var>& a){
	for(vector<Var>::const_iterator i=a.begin(); i<a.end(); i++){
		atoms.push_back(*i);
		addVar(*i);
		modhier.lock()->getModSolver(getParentId())->addVar(*i);
	}

	//Creates a bool-vector mapping each atom to whether it was propagated from above or from this theory
	propfromabove = vector<bool>(atoms.size(), false);
}


/**
 * Sets the id of the parent modal solver. All rigid atoms are then added (possibly again) to the
 * parent solver, as well as this solver as a child and the head as a variable.
 */
void ModSolver::setParent(modindex id){
	parentid = id; hasparent = true;
	pModSolver parent = modhier.lock()->getModSolver(getParentId());
	for(vector<Var>::const_iterator i=atoms.begin(); i<atoms.end(); i++){
		parent->addVar(*i);
	}
	parent->addChild(this->id);
	parent->addVar(head.atom);
}

/**
 * Adds a modal solver as a child of this solver, by id.
 */
void ModSolver::addChild(modindex childid){
	children.push_back(childid);
}

/**
 * Recursively notify all Solvers that parsing has finished
 */
bool ModSolver::finishParsing(){
	bool result = getSolver()->finishParsing();

	for(vmodindex::const_iterator i=getChildren().begin(); result && i<getChildren().end(); i++){
		result = modhier.lock()->getModSolver(*i)->finishParsing();
	}

	init = false;

	return result;
}

/*****************
 * SOLVE METHODS *
 *****************/

/**
 * Tells the root solver to do model expansion on his theory
 */
bool ModSolver::solve(){
	return getSolver()->solve();
}

/*
 * Simplifies PC solver and afterwards simplifies lower modal operators.
 * Returns false if the problem is unsat (and then does not simplify other solvers).
 */
bool ModSolver::simplify(){
	bool result = getSolver()->simplify();

	for(vmodindex::const_iterator i=getChildren().begin(); result && i<getChildren().end(); i++){
		result = modhier.lock()->getModSolver(*i)->simplify();
		//TODO check if this is correct: i think it is not guaranteed that all lower solvers will be searched!
		//It is anyway necessary, because if no search occurs, the modal solvers should still be checked!
		//TODO can this be called multiple times (it shouldn't)
		if(result){
			Clause* c =  modhier.lock()->getModSolver(*i)->propagateDownAtEndOfQueue();
			if(c!=NULL){
				result = false;
				free(c);
			}
		}
	}

	return result;
}

/**
 * Propagates l to be true from the parent modal solver.
 * As long as the PC-solver is still propagating, this solver should not do anything more than store
 * the propagation, as modal satisfiability checking can be much more expensive. So this solver always
 * return NULL (if not, it should return a non-owning pointer).
 */
Clause* ModSolver::propagateDown(Lit l){
	if(modhier.lock()->modes().verbosity>4){
		gprintLit(l); reportf(" propagated down into modal solver %zu.\n", getPrintId());
	}

	adaptValuesOnPropagation(l);

	return NULL;
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
	for(vector<AV>::size_type i=0; i<atoms.size(); i++){
		if(var(l)==atoms[i]){
			propfromabove[i]=true;
			assumptions.push(l);
			break;
		}
	}
}

/**
 * Notifies the modal solver that propagation of the parent solver are finished. At this point, the modal solver
 * will be propagated.
 * Returns an OWNING pointer, because the conflict clause is intended to be used by the PARENT solver
 */
Clause* ModSolver::propagateDownAtEndOfQueue(){
	if(init){
		return NULL;
	}
	if(modhier.lock()->modes().verbosity>4){
		reportf("End of queue propagation down into modal solver %zu.\n", getPrintId());
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

	if(assumptions.size()==getAtoms().size() && (!hasparent || getHeadValue()!=l_Undef)){
		allknown = true;
	}

	bool result = search(assumptions, allknown);

	Clause* confl = analyzeResult(result, allknown);

	if(modhier.lock()->modes().verbosity>4){
		reportf("Finished checking solver %zu: %s.\n", getPrintId(), confl==NULL?"no conflict":"conflict");
	}

	getSolver()->backtrackTo(0);

	return confl;
}

void ModSolver::doUnitPropagation(const vec<Lit>& assumpts){

}

bool ModSolver::search(const vec<Lit>& assumpts, bool search){
	/*
	 * In the end, we would want to propagate level by level, without having to restart the whole process
	 * every time. This requires a startsearch and continuesearch procedure in the SAT-solver
	 * As this is rather tedious, we will delay it until necessary.
	bool result = true;
	if(startindex==-1){
		result = getSolver()->startSearch();
		startindex = 0;
	}
	for(; result && startindex<assumptions.size(); startindex++){
		result = getSolver()->propagate(assumptions[startindex]);
	}
	if(search && result){
		searching = true;
		result = getSolver()->continueSearch();
		searching = false;
	}

	return result;*/

	bool result;
	searching = search;
	if(searching){
		result = getSolver()->solve(assumpts);
	}else{
		result = getSolver()->solvenosearch(assumpts);
	}
	searching = false;
	return result;
}

/**
 * Important, returns a clause constructed to be added to the PARENT solver: the vars are NOT necessarily
 * decision vars in this PC solver
 * Returns owning pointer
 */
Clause* ModSolver::analyzeResult(bool result, bool allknown){
	bool conflict = false;
	Clause* confl = NULL;

	//if no model found and should be sat or if model found, should be unsat and all values are known
	if(getHeadValue()==l_True && !result){
		conflict = true;
	}
	if(getHeadValue()==l_False && result && allknown){
		conflict = true;
	}

	if(conflict){ //conflict between head and body
		//TODO can the clause learning be improved?
		vec<Lit> confldisj;
		if(getHeadValue()!=l_Undef){
			confldisj.push(Lit(getHead(), getHeadValue()==l_True));
		}
		//TODO order of lits in conflict depends on order of assumptions and on order of propagations by parent
		for(int i=0; i<assumptions.size(); i++){
			if(propfromabove[i]){
				confldisj.push(~assumptions[i]);
			}
		}
		assert(confldisj.size()>0);

		confl = Clause_new(confldisj, true);

		if(modhier.lock()->modes().verbosity>=5){
			Print::printClause(*confl, getSolver());
		}
	}

	return confl;
}

/**
 * Returns non-owning pointer
 */
Clause* ModSolver::propagate(Lit l){
	/*if(!searching){
		vector<Lit> v = getSolver()->getDecisions();
		//FIXME propagate up WITH reason
	}*/
	Clause* confl = NULL;
	for(vmodindex::const_iterator i=getChildren().begin(); confl==NULL && i<getChildren().end(); i++){
		confl = modhier.lock()->getModSolver(*i)->propagateDown(l);
	}
	return confl;
}

//In future, we might want to delay effectively propagating and searching in subfolders to the point where the
//queue is empty, so we will need a propagateDown and a propagateDownEndOfQueue
/**
 * Returns non-owning pointer
 */
Clause* ModSolver::propagateAtEndOfQueue(){
	Clause* confl = NULL;
	for(vmodindex::const_iterator i=getChildren().begin(); confl==NULL && i<getChildren().end(); i++){
		confl = modhier.lock()->getModSolver(*i)->propagateDownAtEndOfQueue();
	}
	if(confl!=NULL){
		getSolver()->addLearnedClause(confl);
	}
	return confl;
}

void ModSolver::propagateUp(Lit l, modindex id){
	assert(false);
	//TODO
	//include reason or extend getexplanation to modal solvers (first is maybe best)
	//save id for clause learning
	getSolver()->setTrue(l);
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
	if(modhier.lock()->modes().verbosity>4){
		reportf("Backtracking "); gprintLit(l); reportf(" from above in mod %zu\n", getPrintId());
	}

	if(var(l)==getHead() && getHeadValue()!=l_Undef){
		head.value = l_Undef;
	}
	for(vector<AV>::size_type i=0; i<atoms.size(); i++){
		if(atoms[i]==var(l)){
			if(var(l)==var(assumptions.last())){
				assumptions.pop();
				//startindex--;
				int solverlevel = getSolver()->getLevel(var(l));
				if(solverlevel>=0){ //otherwise it was not propagated!
					getSolver()->backtrackTo(solverlevel);
				}
				propfromabove[i] = false;
				break;
			}else{
#ifndef NDEBUG
				for(int j=0; j<assumptions.size(); j++){
					assert(var(assumptions[j])!=var(l));
				}
#endif
			}
		}
	}
}

void ModSolver::backtrackFromSameLevel(Lit l){
	if(modhier.lock()->modes().verbosity>4){
		reportf("Backtracking "); gprintLit(l); reportf(" from same level in mod %zu\n", getPrintId());
	}

	/*for(vector<AV>::size_type i=0; i<atoms.size(); i++){
		if(atoms[i].atom==var(l)){
			assert(false);
		}
	}*/

	for(vmodindex::const_iterator j=getChildren().begin(); j<getChildren().end(); j++){
		modhier.lock()->getModSolver((*j))->backtrackFromAbove(l);
	}
}

void ModSolver::printModel(){
	getSolver()->printModel();
}
<<<<<<< HEAD:solvers/ModSolver.cpp
=======

void print(const ModSolver& m){
	reportf("ModSolver %zu, parent %zu", m.getPrintId(), m.getParentPrintId() );
	if(m.hasParent()){
		reportf(", head");
		gprintLit(Lit(m.getHead()), m.getHeadValue());
	}
	reportf(", children ");
	for(vmodindex::const_iterator i=m.getChildren().begin(); i<m.getChildren().end(); i++){
		reportf("%d ", *i);
	}
	reportf("\nModal atoms ");
	for(vector<Var>::const_iterator i=m.getAtoms().begin(); i<m.getAtoms().end(); i++){
		reportf("%d ", gprintVar(*i));
	}
	reportf("\nsubtheory\n");
	print(m.getPCSolver());
	reportf("SubSolvers\n");
	for(vmodindex::const_iterator i=m.getChildren().begin(); i<m.getChildren().end(); i++){
		print(*m.getModSolverData().getModSolver(*i));
	}
}

/**
 * Important: PCSolver printclause looks at the signs of the variables, this is not as easy any more
 * in the modal solver
 */
template<class C>
inline void printClause(const C& c)
{
    for (int i = 0; i < c.size(); i++){
        gprintLit(c[i]);
        fprintf(stderr, " ");
    }
}
>>>>>>> public:solvers/ModSolver.cpp
