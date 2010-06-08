#include "ModSolver.hpp"
#include <algorithm>

extern ECNF_mode modes;

//Important: The head variable does not occur in this theory, so should NOT automatically be
//added as a var in it.
/**
 * Constructs a ModSolver, with a given head, index and hierarchy pointer. A PCSolver is initialized.
 */
ModSolver::ModSolver(modindex child, Var head, shared_ptr<ModSolverData> mh):
		id(child), parentid(-1), hasparent(false), init(true),
		head(head), modhier(mh){
	ECNF_mode modescopy(modes);
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
	if(modes.verbosity>5){
		reportf("Var %d added to modal solver %d.\n", var, getPrintId());
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
		atoms.push_back(AV(*i));
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
	for(vector<AV>::const_iterator i=atoms.begin(); i<atoms.end(); i++){
		parent->addVar((*i).atom);
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
 */
bool ModSolver::simplify(){
	bool result = getSolver()->simplify();
	for(vmodindex::const_iterator i=getChildren().begin(); result && i<getChildren().end(); i++){
		result = modhier.lock()->getModSolver(*i)->simplify();
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
	if(modes.verbosity>4){
		gprintLit(l); reportf(" propagated down into modal solver %d.\n", getPrintId());
	}

	adaptValuesOnPropagation(l);

	return NULL;
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
	if(modes.verbosity>4){
		reportf("End of queue propagation down into modal solver %d.\n", getPrintId());
	}
	vec<Lit> assumpts;
	bool allknown = createAssumptions(assumpts);

	/*TODO future:
	bool result;
	if(!allknown){
		result = doUnitPropagation(assumpts);
	}else{
		result = search(assumpts);
	}
	*/

	bool result = search(assumpts, allknown);

	Clause* confl = analyzeResult(result, allknown);

	if(modes.verbosity>4){
		reportf("Finished checking solver %d: %s.\n", getPrintId(), confl==NULL?"no conflict":"conflict");
	}

	getSolver()->backtrackTo(0);

	return confl;
}

bool ModSolver::adaptValuesOnPropagation(Lit l){
	bool contains = false; //Indicates whether l is a rigid atom i this solver

	//Adapt head value
	if(hasparent && getHead()==var(l)){
		assert(getHeadValue()==l_Undef);
		contains = true;
		head.value = !sign(l)?l_True:l_False;
	}

	//adapt rigid atoms value
	for(vector<AV>::size_type i=0; !contains && i<atoms.size(); i++){
		if(var(l)==atoms[i].atom){
			contains = true;
			assert(atoms[i].value==l_Undef);
			if(sign(l)){
				atoms[i].value = l_False;
			}else{
				atoms[i].value = l_True;
			}
			propfromabove[i]=true;
		}
	}

	if(contains){
		propagations.push_back(l);
	}

	return contains;
}

bool ModSolver::createAssumptions(vec<Lit>& assumpts) const{
	if(getHeadValue()==l_Undef){
		return false;
	}

	bool allknown = true;
	for(vector<AV>::const_iterator j=getAtoms().begin(); j<getAtoms().end(); j++){
		if((*j).value!=l_Undef){
			assumpts.push(Lit((*j).atom, (*j).value==l_False));
		}else{
			allknown = false;
		}
	}

	return allknown;
}

void ModSolver::doUnitPropagation(const vec<Lit>& assumpts){

}

bool ModSolver::search(const vec<Lit>& assumpts, bool search){
	searching = search;
	bool result;
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
		if(hasparent && getHeadValue()!=l_Undef){
			confldisj.push(Lit(getHead(), getHeadValue()==l_True));
		}
		//TODO order of lits in conflict depends on order of assumptions and on order of propagations by parent
		for(vector<AV>::size_type j=0; j<getAtoms().size(); j++){
			if(propfromabove[j]){
				confldisj.push(Lit(getAtoms()[j].atom, getAtoms()[j].value==l_True));
			}
		}
		assert(confldisj.size()>0);

		confl = Clause_new(confldisj, true);

		if(modes.verbosity>=5){
			printClause(*confl);
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
	//FIXME or include reason or extend getexplanation to modal solvers (first is maybe best)
	//FIXME save id for clause learning
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
	if(modes.verbosity>4){
		reportf("Backtracking "); gprintLit(l); reportf(" from above in mod %d\n", getPrintId());
	}

	bool contains = false;

	if(var(l)==getHead() && getHeadValue()!=l_Undef){
		head.value = l_Undef;
		contains = true;
		//FIXME: head is not allowed to occur in the theory or lower.
	}
	int c = -1;
	for(vector<AV>::size_type i=0; !contains && i<atoms.size(); i++){
		if(atoms[i].atom==var(l) && atoms[i].value!=l_Undef){
			c = i;
			contains = true;
		}
	}
	if(c!=-1){
		if(atoms[c].value!=l_Undef){
			atoms[c].value = l_Undef;
			int solverlevel = getSolver()->getLevel(var(l));
			if(solverlevel>=0){ //otherwise it was not propagated!
				getSolver()->backtrackTo(solverlevel);
			}
		}
		propfromabove[c] = false;
	}

	if(contains){
		assert(propagations.size()>0 && var(propagations.back())==var(l));
		propagations.pop_back();
	}
}

void ModSolver::backtrackFromSameLevel(Lit l){
	if(modes.verbosity>4){
		reportf("Backtracking "); gprintLit(l); reportf(" from same level in mod %d\n", getPrintId());
	}

	if(var(l)==getHead() && getHeadValue()!=l_Undef){
		head.value = l_Undef;
		//FIXME: head is not allowed to occur in the theory or lower.
	}
	int c = -1;
	for(vector<AV>::size_type i=0; i<atoms.size(); i++){
		if(atoms[i].atom==var(l)){
			c = i;
			break;
		}
	}
	if(c!=-1){
		if(!propfromabove[c] && atoms[c].value!=l_Undef){
			atoms[c].value = l_Undef;
		}
	}

	for(vmodindex::const_iterator j=getChildren().begin(); j<getChildren().end(); j++){
		modhier.lock()->getModSolver((*j))->backtrackFromAbove(l);
	}
}

void ModSolver::printModel(){
	getSolver()->printModel();
}

void print(const ModSolver& m){
	reportf("ModSolver %d, parent %d, head ", m.getPrintId(), m.getParentPrintId() );
	gprintLit(Lit(m.getHead()), m.getHeadValue());
	reportf(", children ");
	for(vmodindex::const_iterator i=m.getChildren().begin(); i<m.getChildren().end(); i++){
		reportf("%d ", *i);
	}
	reportf("\nModal atoms ");
	for(vector<AV>::const_iterator i=m.getAtoms().begin(); i<m.getAtoms().end(); i++){
		reportf("%d ", gprintVar((*i).atom));
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
