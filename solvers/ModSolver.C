#include "ModSolver.h"
#include <algorithm>

extern ECNF_mode modes;

ModSolver::ModSolver(modindex child, Lit head, shared_ptr<ModSolverData> mh):
		id(child), parentid(-1), hasparent(false), head(head), modhier(mh){
	//FIXME ID should be unique to the parent theory and as head of the modal solver. It should not occur in its children, lower or above the parent
	//FIXME there is no use for children rigid atoms that do not occur in the parent theory
	ECNF_mode modescopy(modes);
	if(var(head)>0){ //TODO improve, should not check by head<0
		modescopy.nbmodels = 1;
	}
	solver = new PCSolver(modescopy);
	getSolver()->setModSolver(this);
	//Important: head does NOT occur in the modal theory, so should NOT be added as a var in it.
}

void ModSolver::addVars(vec<Lit>& a){
	for(int i=0; i<a.size(); i++){
		addVar(var(a[i]));
	}
}

void ModSolver::addAtoms(const vector<Var>& a){
	for(int i=0; i<a.size(); i++){
		atoms.push_back(AV(a[i]));
		addVar(a[i]);
		modhier.lock()->getModSolver(getParentId())->addVar(a[i]);
	}
	propfromabove = vector<bool>(atoms.size(), false);
}

void ModSolver::setParent(modindex id){
	parentid = id; hasparent = true;
	shared_ptr<ModSolverData> mh = modhier.lock();
	for(vector<AV>::const_iterator i=atoms.begin(); i<atoms.end(); i++){
		mh->getModSolver(getParentId())->addVar((*i).atom);
	}
	modhier.lock()->getModSolver(id)->addChild(this->id);
	modhier.lock()->getModSolver(id)->addVar(var(head.lit));
}

void copyToVec(const vec<Lit>& v, vector<Lit>& v2){
	for(int i=0; i<v.size(); i++){
	    v2.push_back(v[i]);
	}
}

void ModSolver::addChild(modindex childid){
	//FIXME check that no ancestors become children or that some already have a parent
	children.push_back(childid);
}

bool ModSolver::finishParsing(){
	bool result = getSolver()->finishParsing();

	for(vmodindex::const_iterator i=getChildren().begin(); result && i<getChildren().end(); i++){
		result = modhier.lock()->getModSolver(*i)->finishParsing();
	}

	return result;
}

bool ModSolver::simplify(){
	bool result = getSolver()->simplify();

	for(vmodindex::const_iterator i=getChildren().begin(); result && i<getChildren().end(); i++){
		result = modhier.lock()->getModSolver(*i)->simplify();
	}

	return result;
}

void ModSolver::addVar(Var var){
	getSolver()->addVar(var);
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

bool ModSolver::solve(){
	//FIXME remove head from root
	return getSolver()->solve();
}

Clause* ModSolver::propagateDown(Lit l){
	Clause* confl = NULL;
	bool result = false;
	searching = false;

	if(modes.verbosity>4){
		gprintLit(l); reportf(" propagated down into modal solver %d.\n", getPrintId());
	}

	//Adapt head value
	bool contains = false;
	if(var(getHead())==var(l)){
		contains = true;
		assert(getHeadValue()==l_Undef);
		head.value = l==getHead()?l_True:l_False;
	}

	//adapt rigid atoms value
	for(int i=0; i<atoms.size(); i++){
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

	if(!contains){
		return confl;
	}

	//TODO: make 2 modsolvers, one to be the root
	//If all rigid atoms and head are known, do search in this solver
	bool allknown = true;

	vec<Lit> assumpts;
	if(getHeadValue()==l_Undef){
		allknown = false;
	}

	//reportf("Adding assumptions ");

	for(vector<AV>::const_iterator j=getAtoms().begin(); allknown && j<getAtoms().end(); j++){
		if((*j).value==l_Undef){
			allknown = false;
		}else{
			//important: prevent double propagations! Only add what is not yet known by the solver
			if(getSolver()->value((*j).atom)==l_Undef){
				Lit l = Lit((*j).atom, (*j).value==l_False);
				assumpts.push(l);
				//gprintLit(l); reportf(" ");
			}
		}
	}
	//reportf("\n");
	if(!allknown){
		//FIXME this code is not correct
		//FIXME propagation should only occur for existential theories
		//TODO make head a VAR, not a literal
		/*//do propagations
		result = getSolver()->solvenosearch(assumpts);
		if(!result){
			//FIXME UNSAT found, so can certainly do something upwards!
		}
		getSolver()->backtrackTo(0);
	}

	//recheck whether all is known after propagation
	for(vector<AV>::const_iterator j=getAtoms().begin(); j<getAtoms().end(); j++){
		if((*j).value==l_Undef){*/
			return confl;
		/*}*/
	}

	if(modes.verbosity>4){
		reportf("Checking lower solver %d.\n", getPrintId());
	}

	//FIXME: he starts searching before head is known, so any derivation will be a propagation,
	//no a conflict!!!! => he now only starts when head is known

	assert(hasparent);
	searching = true;
	result = getSolver()->solve(assumpts);

	//FIXME: returns a conflict which can be based on decision variables only,
	//so clause learning will crash.
	//IMPORTANT INVARIANT: THE LAST DECISION VARIABLE SHOULD ALWAYS BE INCLUDED IN THE CONFLICT CLAUSE
	//IMPORTANT INVARIANT: CONFLICTS HAVE TO BE DETECTED BY PROPAGATION: BACKTRACK UNTIL PREVIOUS CHOICE
	if((result && getHeadValue()!=l_True) || (!result && getHeadValue()!=l_False)){
		//conflict between head and body
		//FIXME good clause learning
		vec<Lit> confldisj;
		confldisj.push(l);
		if(var(l)!=var(getHead())){
			confldisj.push(getHead());
		}
		//PROBLEM: order of lits in conflict depends on order of assumptions and on order of propagations by parent
		for(vector<AV>::const_iterator j=getAtoms().begin(); j<getAtoms().end(); j++){
			if(var(l)!=(*j).atom){
				confldisj.push(Lit((*j).atom, (*j).value==l_False));
			}
		}
		confl = Clause_new(confldisj, true);
	}
	if(modes.verbosity>4){
		reportf("Finished checking lower solver %d: %s.\n", getPrintId(), confl==NULL?"no conflict":"conflict");
	}

	getSolver()->backtrackTo(0);
	return confl;
}

Clause* ModSolver::propagate(Lit l){
	Clause* confl = NULL;

	if(!searching){
		vector<Lit> v = getSolver()->getDecisions();
		//FIXME propagate up WITH reason
	}

	//FIXME FIXME: IMPORTANT! Problem is that unit clauses might be added (and propagated) before
	//the children have been loaded!!!!!
	for(vmodindex::const_iterator i=getChildren().begin(); confl==NULL && i<getChildren().end(); i++){
		confl = modhier.lock()->getModSolver(*i)->propagateDown(l);
	}
	if(confl!=NULL){
		/*
		 * Due to current incomplete propagation, the conflict could possibly have been derived at an earlier level.
		 * So check for this and first backtrack to that level.
		 */
		int lvl = 0;
		for (int i = 0; i < confl->size(); i++){
			int litlevel = getSolver()->getLevel(var(confl->operator [](i)));
			if (litlevel > lvl){
				lvl = litlevel;
			}
		}
		getSolver()->backtrackTo(lvl);

		if(modes.verbosity>4){
			reportf("Level %d in modal %d.\n", lvl, getPrintId());
		}
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

	if(var(l)==var(getHead()) && getHeadValue()!=l_Undef){
		head.value = l_Undef;
		//FIXME: head is not allowed to occur in the theory or lower.
	}
	int c = -1;
	for(int i=0; i<atoms.size(); i++){
		if(atoms[i].atom==var(l)){
			c = i;
			break;
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

	for(vmodindex::const_iterator j=getChildren().begin(); j<getChildren().end(); j++){
		modhier.lock()->getModSolver((*j))->backtrackFromAbove(l);
	}
}

void ModSolver::backtrackFromSameLevel(Lit l){
	//reportf("Backtracking "); gprintLit(l); reportf(" from same level in mod %d\n", getPrintId());

	if(var(l)==var(getHead()) && getHeadValue()!=l_Undef){
		head.value = l_Undef;
		//FIXME: head is not allowed to occur in the theory or lower.
	}
	int c = -1;
	for(int i=0; i<atoms.size(); i++){
		if(atoms[i].atom==var(l)){
			c = i;
			break;
		}
	}
	if(c!=-1){
		int solverlevel = getSolver()->getLevel(var(l));
		if(solverlevel>=0){ //otherwise it was not propagated!
			getSolver()->backtrackTo(solverlevel);
		}
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
	gprintLit(m.getHead(), m.getHeadValue());
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
