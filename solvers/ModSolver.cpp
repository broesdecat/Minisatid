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

	//Create a bool-vector mapping each atom to whether it was propagated from above or from this
	//own theory
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
 * Recursively notify all PCSolvers that parsing has finished
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

//Responsible for printing models and finding multiple ones!
//Only used by root solver currently
bool ModSolver::solve(){
	return solver->solve();
}

/*
 * First simplifies PC solver, afterwards simplifies lower modal operators.
 */
bool ModSolver::simplify(){
	bool result = getSolver()->simplify();
	for(vmodindex::const_iterator i=getChildren().begin(); result && i<getChildren().end(); i++){
		result = modhier.lock()->getModSolver(*i)->simplify();
	}
	return result;
}

/**
 * Returns non-owning pointer
 */
Clause* ModSolver::propagateDown(Lit l){
	if(modes.verbosity>4){
		gprintLit(l); reportf(" propagated down into modal solver %d.\n", getPrintId());
	}

	adaptValuesOnPropagation(l);

	return NULL;
}

/**
 * Returns non-owning pointer
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

	if(!allknown){
		return NULL;
	}

	bool result = search(assumpts);

	Clause* confl = analyzeResult(result, allknown);
	solver->addLearnedClause(confl);

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
	for(vector<AV>::size_type i=0; i<atoms.size(); i++){
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

	/*reportf("PROPAGATION: ");
	gprintLit(l);
	reportf("\n");
	propagations.push_back(l);*/

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

bool ModSolver::search(const vec<Lit>& assumpts){
	searching = true;
	bool result = getSolver()->solve(assumpts);
	searching = false;
	return result;
}

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
		//FIXME good clause learning
		//Only have to be literals that were DOWN propagated!
		vec<Lit> confldisj;
		if(getHeadValue()!=l_Undef){
			confldisj.push(Lit(getHead()));
		}
		//TODO order of lits in conflict depends on order of assumptions and on order of propagations by parent
		for(vector<AV>::const_iterator j=getAtoms().begin(); j<getAtoms().end(); j++){
			confldisj.push(Lit((*j).atom, (*j).value==l_False));
		}
		confl = Clause_new(confldisj, true);
		if(modes.verbosity>=5){
			solver->printClause(*confl);
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
	//reportf("Backtracking "); gprintLit(l); reportf(" from above in mod %d\n", getPrintId());

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
		/*reportf("BACKTRACK: ");
		gprintLit(l);
		reportf("\n");
		assert(propagations.size()>0 && var(propagations.back())==var(l));
		propagations.pop_back();*/

		if(atoms[c].value!=l_Undef){
			atoms[c].value = l_Undef;
			int solverlevel = getSolver()->getLevel(var(l));
			if(solverlevel>=0){ //otherwise it was not propagated!
				getSolver()->backtrackTo(solverlevel);
			}
		}
		propfromabove[c] = false;
	}

	/*for(vmodindex::const_iterator j=getChildren().begin(); j<getChildren().end(); j++){
		modhier.lock()->getModSolver((*j))->backtrackFromAbove(l);
	}*/
}

void ModSolver::backtrackFromSameLevel(Lit l){
	//reportf("Backtracking "); gprintLit(l); reportf(" from same level in mod %d\n", getPrintId());

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
