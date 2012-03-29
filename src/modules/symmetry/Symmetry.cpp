/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */

#include "Symmetry.hpp"

#include "satsolver/SATSolver.hpp" // TODO remove dependency (for querying clause info)

using namespace std;
using namespace MinisatID;
using namespace Minisat;

SymmetryData::SymmetryData(int nVars, const InnerSymmetry& symmetry): sym(symmetry){
	for(auto i=sym.symmetry.cbegin(); i!=sym.symmetry.cend(); ++i){
		if(i->first!=i->second){
			continue;
		}
		inverse.symmetry[i->second] = i->first;
	}
}

SymmetryPropagator::SymmetryPropagator(PCSolver* solver, const InnerSymmetry& sym)
		: Propagator(solver, "symmetry propagator"), symmetry(solver->nVars(), sym) {
	amountNeededForActive = 0;
	reasonOfPermInactive = lit_Undef;
	nextToPropagate = 0;

	for(auto i=symmetry.getSymmetryMap().cbegin(); i!=symmetry.getSymmetryMap().cend(); ++i){
		getPCSolver().accept(this, i->first, PRIORITY::FAST);

		if(useVarOrderOptimization() && i->first==(not i->second)){ // phase-changing optimization
			getPCSolver().varReduceActivity(var(i->first));
		}
	}

#ifdef DEBUG
	testSymmetry();
#endif
}

void SymmetryPropagator::print() {
	// TODO print
/*	printf("Symmetry: %i - neededForActive: %i\n", getId(), amountNeededForActive);
	for (int i = 0; i < sym.size(); ++i) {
		if (sym[i] != toLit(i)) {
			printf("%i->%i | ", i, toInt(sym[i]));
		}
	}
	printf("\n notifiedLits: ");
	for (int i = 0; i < notifiedLits.size(); ++i) {
		printf("%i:", toInt(notifiedLits[i]));
		getPCSolver().testPrintValue(notifiedLits[i]);
		printf(" | ");
	}
	printf("\n");
	printf("amountNeededForActive: %i | firstNotPropagated: %i\n", amountNeededForActive, nextToPropagate);*/
}

#define getLit(clause, nb) (getPCSolver().getClauseLit(clause, nb))
#define lowerLevel(x, y) (getPCSolver().getLevel(var(x))<getPCSolver().getLevel(var(y)))

bool SymmetryPropagator::getSymmetricalClause(std::vector<Lit>& in_clause, std::vector<Lit>& out_clause) {
	out_clause = in_clause;
	bool mapstoitself = true;
	for (int i = in_clause.size() - 1; i >= 0; --i) {
		if (getSymmetrical(in_clause[i]) != out_clause[i]) {
			out_clause[i] = getSymmetrical(in_clause[i]);
			mapstoitself = false;
		}
	}
	return not mapstoitself;
}

void SymmetryPropagator::getSymmetricalClause(const rClause& in_clause, std::vector<Lit>& out_clause) {
	auto insize = getPCSolver().getClauseSize(in_clause);
	out_clause.clear();
	for (int i = insize-1; i >= 0; --i) {
		out_clause.push_back(getSymmetrical(getLit(in_clause, i)));
	}
}

//	@pre:	in_clause is clause without true literals
//	@post: 	out_clause is one of three options, depending on the number of unknown literals:
//			all false literals with first most recent and second second recent
//			first literal unknown, rest false and second most recent
//			first two literals unknown
void SymmetryPropagator::getSortedSymmetricalClause(const rClause& in_clause, std::vector<Lit>& out_clause) {
	auto insize = getPCSolver().getClauseSize(in_clause);
	assert(insize >= 2);
	int first = 0;
	int second = 1;
	out_clause.clear();
	out_clause.push_back(getSymmetrical(getLit(in_clause, 0)));
	for (int i = 1; i < insize; ++i) {
		out_clause.push_back(getSymmetrical(getLit(in_clause, i)));
		MAssert(value(out_clause[i]) != l_True);
		if (value(out_clause[first]) != l_Undef && (value(out_clause[i]) == l_Undef || lowerLevel(out_clause[first], out_clause[i]))) {
			second = first;
			first = i;
		} else if (value(out_clause[second]) != l_Undef && (value(out_clause[i]) == l_Undef || lowerLevel(out_clause[second], out_clause[i]))) {
			second = i;
		}
	}

	// note: swapping the final literals to their place is pretty tricky. Imagine for instance the case where first==0 or second==1 ;)
	if (first != 0) {
		Lit temp = out_clause[0];
		out_clause[0] = out_clause[first];
		out_clause[first] = temp;
	}
	assert(second != first);
	if (second == 0) {
		second = first;
	}
	if (second != 1) {
		Lit temp = out_clause[1];
		out_clause[1] = out_clause[second];
		out_clause[second] = temp;
	}
}

Lit SymmetryPropagator::getNextToPropagate() {
	if (!isActive() && not useInactivePropagationOptimization()) {
		return lit_Undef;
	}
	while (nextToPropagate < notifiedLits.size() && (getPCSolver().isDecided(var(notifiedLits[nextToPropagate])) || value(getSymmetrical(notifiedLits[nextToPropagate])) == l_True)) {
		++nextToPropagate;
	}
	if (nextToPropagate == notifiedLits.size()) {
		return lit_Undef;
	} else if (isActive()) {
		return notifiedLits[nextToPropagate];
	} else {
		MAssert(useInactivePropagationOptimization());
		int nextToPropagateInactive = nextToPropagate;
		while (nextToPropagateInactive < notifiedLits.size() && not canPropagate(notifiedLits[nextToPropagateInactive])) {
			++nextToPropagateInactive;
		}
		if (nextToPropagateInactive == notifiedLits.size()) {
			return lit_Undef;
		} else {
			return notifiedLits[nextToPropagateInactive];
		}
	}
}

bool SymmetryPropagator::canPropagate(Lit l) {
	if (getPCSolver().isDecided(var(l)) || value(getSymmetrical(l)) == l_True) {
		return false;
	}
	if (getPCSolver().getLevel(var(l)) == 0) {
		return true;
	}
	auto cref = getPCSolver().getExplanation(l);
	MAssert(cref!=nullPtrClause);
	bool noUndefYet = true;
	for (int i = 0; i < getPCSolver().getClauseSize(cref); ++i) {
		auto confllit = getLit(cref, i);
		if (value(getSymmetrical(confllit)) == l_True) {
			return false;
		} else if (value(getSymmetrical(confllit)) == l_Undef) {
			if (noUndefYet) {
				noUndefYet = false;
			} else {
				return false;
			}
		}
	}
	return true;
}

rClause SymmetryPropagator::notifypropagate(){
	while(hasNextProp()){
		auto p = getNextProp();
		notifyEnqueued(p);
	}
	auto confl = nullPtrClause;
	// weakly active symmetry propagation: the condition qhead==trail.size() makes sure symmetry propagation is executed after unit propagation
	Lit orig = lit_Undef;
	if(isActive()){
		orig = getNextToPropagate();
		if(orig!=lit_Undef){
			confl = propagateSymmetrical(orig);
		}
	}//else{
		//if(useInactivePropagationOptimization()){
		//	inactiveSyms.push(sym);
		//}
	//}
	// TODO in fact, want to only propagate active symmetries first (which is cheap) and possibly later check the inactive ones too
	// Should implement as dynamic priority change of propagator
	//for( int i=inactiveSyms.size()-1; useInactivePropagationOptimization() && qhead==trail.size() && confl==CRef_Undef && i>=0; --i){
	//	Symmetry* sym = inactiveSyms[i];
	//	Lit orig = sym->getNextToPropagate();
	//	if(orig!=lit_Undef){
	//		confl = propagateSymmetrical(sym,orig);
	//	}
	//}
	return confl;
}

void SymmetryPropagator::notifyEnqueued(const Lit& l) {
	// Start with latest not yet propagated literals
	assert(getSymmetrical(l) != l);
	assert(value(l) == l_True);
	notifiedLits.push_back(l);
	if (isPermanentlyInactive()) {
		return;
	}
	auto inverse = getInverse(l);
	auto symmetrical = getSymmetrical(l);
	if (getPCSolver().isDecided(var(inverse))) {
		if (value(inverse) == l_True) { //invar: value(l)==l_True
			--amountNeededForActive;
		} else {
			assert(getPCSolver().value(inverse) == l_False);
			reasonOfPermInactive = l;
		}
	}
	if (getPCSolver().isDecided(var(l))) {
		if (value(symmetrical) == l_Undef) {
			++amountNeededForActive;
		} else if (value(symmetrical) == l_False) {
			reasonOfPermInactive = l;
		}
		// else value(symmetrical) is true
	}
}

// Store activity and number of needed literals
void SymmetryPropagator::notifyNewDecisionLevel(){
	activityTrail.push_back(reasonOfPermInactive);
	amountNeededTrail.push_back(amountNeededForActive);
	notifiedLitTrail.push_back(notifiedLits);
}

// Reset activity and number of needed literals
void SymmetryPropagator::notifyBacktrack(int untillevel, const Lit& decision) {
	nextToPropagate = 0;
	reasonOfPermInactive = activityTrail[untillevel];
	activityTrail.resize(untillevel+1);
	amountNeededForActive = amountNeededTrail[untillevel];
	amountNeededTrail.resize(untillevel+1);
	notifiedLits = notifiedLitTrail[untillevel];
	notifiedLitTrail.resize(untillevel+1);
}

bool SymmetryPropagator::isActive() {
	return amountNeededForActive == 0 && !isPermanentlyInactive(); // Laatste test is nodig voor phase change symmetries
}

bool SymmetryPropagator::isPermanentlyInactive() {
	return reasonOfPermInactive != lit_Undef;
}

bool SymmetryPropagator::testIsActive(const std::vector<Lit>& trail) {
	std::set<Lit> trailCopy;
	for (int i = 0; i < trail.size(); ++i) {
		trailCopy.insert(trail[i]);
	}
	for (int i = 0; i < trail.size(); ++i) {
		Lit l = trail[i];
		if (getPCSolver().isDecided(var(l))) {
			if (!trailCopy.count(getSymmetrical(l))) {
				return false;
			}
		}
	}
	return true;
}

bool SymmetryPropagator::testIsPermanentlyInactive(const std::vector<Lit>& trail) {
	std::set<Lit> trailCopy;
	for (int i = 0; i < trail.size(); ++i) {
		trailCopy.insert(trail[i]);
	}
	for (int i = 0; i < trail.size(); ++i) {
		Lit l = trail[i];
		if (getPCSolver().isDecided(var(l))) {
			if (trailCopy.count(~getSymmetrical(l))) {
				return true;
			}
		}
	}
	return false;
}

rClause SymmetryPropagator::propagateSymmetrical(const Lit& l){
	MAssert(value(getSymmetrical(l))!=l_True);

	InnerDisjunction implic;
	if(getPCSolver().getLevel(var(l))==0){
		implic.literals.push_back(getSymmetrical(l));
		implic.literals.push_back(~l);
	}else{
		auto reason = getPCSolver().getExplanation(l);
		MAssert(reason!=CRef_Undef);
		getSortedSymmetricalClause(reason, implic.literals);
	}
	auto symlit = implic.literals[0];
	auto neglit = implic.literals[1];
	auto level = getPCSolver().getLevel(var(neglit));
	if(getPCSolver().getCurrentDecisionLevel()>level){
		getPCSolver().backtrackTo(level); // Backtrack verplicht om de watches op het juiste moment op de clause te zetten
	}
	MAssert(value(symlit)!=l_True);
	MAssert(value(neglit)==l_False);

	auto clause = getPCSolver().createClause(implic, true);
	if(value(symlit)==l_Undef){
		if(addPropagationClauses()){
			getPCSolver().addLearnedClause(clause);
		}
		getPCSolver().setTrue(symlit,this, clause);
	}else{
		MAssert(value(symlit)==l_False);
		if(addConflictClauses()){
			getPCSolver().addLearnedClause(clause);
		}
		return clause;
	}
	return nullPtrClause;
}

void SymmetryPropagator::testSymmetry(){
	auto nbclauses = getPCSolver().getSATSolver()->nbClauses();
	for(int i=0; i<nbclauses; ++i){
		auto cref = getPCSolver().getSATSolver()->getClause(i);
		std::set<Lit> orig_set;
		std::set<Lit> sym_set;
		for(int j=0; j<getPCSolver().getClauseSize(cref);++j){
			auto lit = getPCSolver().getClauseLit(cref, j);
			orig_set.insert(lit);
			sym_set.insert(getSymmetrical(lit));
		}
		bool hasSymmetrical = sym_set==orig_set;
		for(int j=0; !hasSymmetrical && j<nbclauses; ++j){
			auto symmcref = getPCSolver().getSATSolver()->getClause(j);
			sym_set.clear();
			if(getPCSolver().getClauseSize(cref)==getPCSolver().getClauseSize(symmcref)){
				for(int k=0; k<getPCSolver().getClauseSize(cref); ++k){
					sym_set.insert(getInverse(getPCSolver().getClauseLit(symmcref, k)));
				}
				hasSymmetrical = sym_set==orig_set;
			}
		}
		MAssert(hasSymmetrical);
	}
}

void SymmetryPropagator::testActivityForSymmetries(){
	const auto& trail = getPCSolver().getTrail();
	if(isPermanentlyInactive()!=testIsPermanentlyInactive(trail) ){
		printf("ERROR: not sure if a symmetry is permanently inactive...\n");
		printf("symmetry says: %i - ",isPermanentlyInactive() );
		printf("test says: %i\n",testIsPermanentlyInactive(trail) );
		print();
		// TODO printtrail
		MAssert(false);
	}
	if(isActive()!=testIsActive(trail) ){
		printf("ERROR: not sure if a symmetry is active...\n");
		printf("symmetry says: %i - ",isActive() );
		printf("test says: %i\n",testIsActive(trail) );
		print();
		for(int j=0; j<trail.size(); ++j){
			printf("%i | %i | %i\n",getPCSolver().getLevel(var(trail[j])),toInt(trail[j]),getPCSolver().isDecided(var(trail[j])));
		}
		MAssert(false);
	}
}


// Symmetry is a commented line with cycles.
// The line starts with "c", followed by a blank, followed by the permutation cycles comprised of literals, followed by a blank followed by a zero.
// Every literal in a cycle is either a positive or negative literal.
// The positive literal is itself, the negative literal is the positive literal + the total number of variables.
// e.g.: c (1 2 3)(4 5 6) 0 denotes the symmetry 1->2, 2->3, 3->1, -1->-2, -2->-3, -3->-1.
template<class B, class Solver>
static void parse_SYMMETRY_main(B& in, Solver& S) {
	// TODO implement parsing
/*	int nrVars=S.nVars();
	assert(nrVars>0);
	assert(*in=='[');
	++in; // skipping the "["
	++in; // jumping to next line
	int start,first, second;
	while(true){
		vec<Lit> symFrom, symTo;
		while(*in=='('){
			++in;
			start = parseInt(in);
			if(start>nrVars){ //adjusting shatter's format
				start=nrVars-start;
			}
			second = start;
			assert(*in==',');
			while(*in==','){
				++in;
				first = second;
				second = parseInt(in);
				if(second>nrVars){ //adjusting shatter's format
					second=nrVars-second;
				}
				if(second>= -nrVars && first>= -nrVars){ //check for phase shift symmetries
					symFrom.push(mkLit(abs(first)-1,first<0));
					symTo.push(mkLit(abs(second)-1,second<0));
				}else{
					assert(second< -nrVars && first< -nrVars);
				}
			}
			assert(*in==')'); ++in;
			first = second;
			second = start;
			if(second>=-nrVars && first>=-nrVars){ //check for phase shift symmetries
				symFrom.push(mkLit(abs(first)-1,first<0));
				symTo.push(mkLit(abs(second)-1,second<0));
			}else{
				assert(second< -nrVars && first< -nrVars);
			}
		}
		S.addSymmetry(symFrom,symTo);
		if(*in==','){
			++in; ++in; assert(*in=='(');
		}else{
			break;
		}
	}*/
 }
