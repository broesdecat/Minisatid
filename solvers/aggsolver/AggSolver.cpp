//--------------------------------------------------------------------------------------------------
//    Copyright (c) 2009-2010, Broes De Cat, K.U.Leuven, Belgium
//    
//    Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
//    associated documentation files (the "Software"), to deal in the Software without restriction,
//    including without limitation the rights to use, copy, modify, merge, publish, distribute,
//    sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
//    furnished to do so, subject to the following conditions:
//    
//    The above copyright notice and this permission notice shall be included in all copies or
//    substantial portions of the Software.
//    
//    THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
//    NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
//    NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
//    DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
//    OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
//--------------------------------------------------------------------------------------------------

/************************************************************************************
 Copyright (c) 2006-2009, Maarten Mariën

 Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
 associated documentation files (the "Software"), to deal in the Software without restriction,
 including without limitation the rights to use, copy, modify, merge, publish, distribute,
 sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
 furnished to do so, subject to the following conditions:

 The above copyright notice and this permission notice shall be included in all copies or
 substantial portions of the Software.

 THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
 NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
 DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
 OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 **************************************************************************************************/

#include "solvers/aggsolver/AggSolver.hpp"

#include "solvers/utils/Utils.hpp"
#include "solvers/utils/Print.hpp"

#include "solvers/pcsolver/PCSolver.hpp"

#include "solvers/aggsolver/AggComb.hpp"

#include "solvers/aggsolver/FullyWatched.hpp"
#include "solvers/aggsolver/PartiallyWatched.hpp"

#include <algorithm>

#include <stdint.h>
#include <inttypes.h>
#include <limits.h>
#include <cmath>

AggSolver::AggSolver(pPCSolver s) :
	SolverModule(s), propagations(0) {
	int count = 0;
}

AggSolver::~AggSolver() {
	deleteList<aggs> (sets);
	deleteList<AggReason> (aggreason);
	deleteList<Watch>(permwatches);
}

void AggSolver::notifyVarAdded(uint64_t nvars) {
	assert(headwatches.size() < nvars);
	headwatches.resize(nvars, NULL);
	permwatches.resize(nvars);
	tempwatches.resize(2 * nvars);
	aggreason.resize(nvars, NULL);
	network.resize(nvars);
	assigns.resize(nvars, l_Undef);
}

///////
// WATCH MANIPULATION
///////

void AggSolver::setHeadWatch(Var head, Agg* agg) {
	headwatches[head] = agg;
}

void AggSolver::removeHeadWatch(Var x) {
	//delete headwatches[x];
	headwatches[x] = NULL;
	getPCSolver()->removeAggrHead(x);
}

void AggSolver::addPermWatch(Var v, pw w) {
	permwatches[v].push_back(w);
}

void AggSolver::addTempWatch(const Lit& l, pw w) {
	//reportf("Watch added: "); gprintLit(l); reportf("\n");
	tempwatches[toInt(l)].push_back(w);
}

inline pagg AggSolver::getAggWithHead(Var v) const {
	assert(headwatches[v] != NULL);
	return headwatches[v];
}

///////
// MAIN OPERATIONS
///////


bool AggSolver::addSet(int setid, const vector<Lit>& lits, const vector<Weight>& weights) {
	assert(lits.size()==weights.size());

	if (lits.size() == 0) {
		char s[100]; sprintf(s, "Set nr. %d is empty.\n", setid);
		throw idpexception(s);
	}

	if (parsedsets.find(setid)!=parsedsets.end()) {
		char s[100];
		sprintf(s, "Set nr. %d is defined more than once.\n", setid);
		throw idpexception(s);
	}

	vector<WL> lw;
	for (vsize i = 0; i < lits.size(); i++) {
#ifdef INTWEIGHT
		if (weights[i] == INT_MAX || weights[i] == INT_MIN) {
			throw idpexception(
					"Weights equal to or larger than the largest integer number "
						"are not allowed in limited precision.\n");
		}
#endif
		lw.push_back(WL(lits[i], weights[i]));
	}

	parsedsets[setid] = new ParsedSet(setid, lw);

	if (verbosity() >= 5) { // Print information on added set
		reportf("Added set %d: ", setid);
		vector<Weight>::const_iterator w = weights.begin();
		bool begin = true;
		for (vsize i = 0; i < lits.size(); i++, w++) {
			if (begin) {
				begin = false;
			} else {
				reportf(", ");
			}
			reportf("%d=%s", gprintVar(var(lits[i])), printWeight(*w).c_str());
		}
		reportf("\n");
	}

	return true;
}

bool AggSolver::addAggrExpr(Var headv, int setid, Weight bound,	AggSign boundsign, AggType type, AggSem headeq) {
	assert(type==MIN || type==MAX || type==CARD || type==SUM || type==PROD);

	if (parsedsets.find(setid)==parsedsets.end()) { //Exception if set already exists
		char s[100];
		sprintf(s, "Set nr. %d is used, but not defined yet.\n", setid);
		throw idpexception(s);
	}
	if (headv<0) { //Exception if head is neg
		char s[100];
		sprintf(s, "Heads have to be positive, which is violated for head %d.\n", headv);
		throw idpexception(s);
	}

	ppaset set = parsedsets[setid];

	// Check whether the head occurs in the body of the set, which is no longer allowed
	// TODO zet in file huidige invoerformaat, zodat de grounder dat kan garanderen
	for(vsize i=0; i<set->getWL().size() ;i++){
		if(var(set->getWL()[i])==headv){ //Exception if head occurs in set itself
			char s[100];
			sprintf(s, "Set nr. %d contains a literal of atom %d, the head of an aggregate, which is not allowed.\n", setid, gprintVar(headv));
			throw idpexception(s);
		}
	}

	//Check that not aggregates occur with the same heads
	for(map<int, ppaset>::const_iterator i=parsedsets.begin(); i!=parsedsets.end(); i++){
		for(vsize j=0; j<(*i).second->getAgg().size(); j++){
			if(var((*i).second->getAgg()[j]->getHead())==headv){ //Exception if two agg with same head
				char s[100];
				sprintf(s, "At least two aggregates have the same head(%d).\n", gprintVar(headv));
				throw idpexception(s);
			}
		}
	}

#ifdef DEBUG
	if(type == CARD){ //Check if all card weights are 1
		for(vwl::size_type i=0; i<parsedsets[setid]->getWL().size(); i++) {
			if(parsedsets[setid]->getWL()[i].getWeight()!=1) {
				reportf("Cardinality was loaded with wrong weights");
				assert(false);
			}
		}
	}
#endif

	// As an approximation because each literal would occur n times (TODO better approximation?), we bump n times
	//ORIG: getPCSolver()->varBumpActivity(headv);
	for(int i=0; i<log(set->getWL().size())+1; i++){
		getPCSolver()->varBumpActivity(headv);
		for(int j=0; j<set->getWL().size(); j++){
			getPCSolver()->varBumpActivity(var(set->getWL()[i]));
		}
	}

	//the head of the aggregate
	Lit head = mkLit(headv, false);
	new ParsedAgg(bound, boundsign, head, headeq, parsedsets[setid], type);

	if (verbosity() >= 5) { //Print info on added aggregate
		reportf("Added %s aggregate with head %d on set %d, %s %s of type ",
				headeq == DEF?"defined":"completion", gprintVar(headv), setid,
				boundsign==LB?"AGG <=":"AGG >=", printWeight(bound).c_str());
		switch(type){
			case SUM: reportf("SUM"); break;
			case CARD: reportf("CARD"); break;
			case MIN: reportf("MIN"); break;
			case MAX: reportf("MAX"); break;
			case PROD: reportf("PROD"); break;
		}
		reportf(".\n");
	}

	return true;
}

void AggSolver::finishParsing(bool& present, bool& unsat) {
	notifyInitialized();

	unsat = false;
	present = true;

	if (parsedsets.size() == 0) {
		present = false;
		return;
	}

	if (verbosity() >= 3) {
		reportf("Initializing aggregates\n");
	}

	// Initialize all parsed sets
	for(map<int, ppaset>::const_iterator i=parsedsets.begin(); i!=parsedsets.end(); i++){
		bool foundunsat = finishSet((*i).second);
		if (foundunsat){
			if (verbosity() >= 3) {
				reportf("Initializing aggregates finished, unsat detected.\n");
			}
			unsat = true;
			return;
		}
	}
	deleteList<paset>(parsedsets);

	vsize max = 0, min = 0, card = 0, prod = 0, sum = 0;
	int agg = 0, setlits = 0, nbsets = sets.size();
	for(vsize i=0; i<sets.size(); i++){
		agg += sets[i]->getAgg().size();
		setlits += sets[i]->getWL().size();
		switch(sets[i]->getType()){
			case MIN: min++; break;
			case MAX: max++; break;
			case PROD: prod++; break;
			case SUM: sum++; break;
			case CARD: card++; break;
		}
	}

	if(agg==0){
		if(verbosity()>=3){
			reportf("Initializing aggregates finished, no aggregates present after initialization.\n");
		}
		present = false;
		return;
	}

	if (verbosity() >= 1) {
		reportf("| Number of minimum exprs.:     %4zu                                          |\n", min);
		reportf("| Number of maximum exprs.:     %4zu                                          |\n", max);
		reportf("| Number of sum exprs.:         %4zu                                          |\n", sum);
		reportf("| Number of product exprs.:     %4zu                                          |\n", prod);
		reportf("| Number of cardinality exprs.: %4zu                                          |\n", card);

		reportf("| Over %4d sets, aggregate set avg. size: %7.2f lits.                      |\n",
				nbsets,(double)setlits/(double)(nbsets));
	}
	if (verbosity() >= 3) {
		reportf("Aggregates are present after initialization:\n");
		for (vpaggs::const_iterator i=sets.begin(); i<sets.end(); i++) {
			for (vpagg::const_iterator j = (*i)->getAgg().begin(); j < (*i)->getAgg().end(); j++) {
				Aggrs::printAgg(**j, true);
			}
		}

		for (vsize i = 0; i < nVars(); i++) {
			reportf("Watches of var %d:\n", gprintVar(i));
			if (headwatches[i] != NULL) {
				reportf("   headwatch\n");
				reportf("      ");
				Aggrs::printAgg(headwatches[i]->getAggComb(), true);
			}

			if (verbosity() >= 6) {
				reportf("   bodywatches\n");
				for (vsize j = 0; j < permwatches[i].size(); j++) {
					reportf("      ");
					Aggrs::printAgg((permwatches[i][j])->getAggComb(), true);
				}
				for (vsize j = 0; j < tempwatches[i].size(); j++) {
					reportf("      ");
					Aggrs::printAgg((tempwatches[i][j])->getAggComb(), true);
				}
			}
		}
	}
}

bool AggSolver::finishSet(ppaset set){
	bool unsat = false;

	//Partition the aggregates according to their type
	map<AggType, vppagg> partaggs;
	for(vppagg::const_iterator i = set->getAgg().begin(); i<set->getAgg().end(); i++) {
		partaggs[(*i)->getType()].push_back(*i);
	}

	//Initialize the different sets
	for(map<AggType, vppagg>::const_iterator i=partaggs.begin(); !unsat && i!=partaggs.end(); i++){
		if((*i).second.size()==0){
			continue;
		}

		switch((*i).first){
			case MIN:  unsat = constructMinSet(set, (*i).second); break;
			case MAX:  unsat = constructMaxSet(set, (*i).second); break;
			case CARD: unsat = constructCardSet(set, (*i).second); break;
			case SUM:  unsat = constructSumSet(set, (*i).second); break;
			case PROD: unsat = constructProdSet(set, (*i).second); break;
		}
	}

	return unsat;
}

//gets OWNING pointer to ca
bool AggSolver::initCalcAgg(CalcAgg* ca, vppagg aggs){
	for(vsize i=0; i<aggs.size(); i++){
		ca->addAgg(new Agg(aggs[i]->getBound(), aggs[i]->getSign(), aggs[i]->getHead(), aggs[i]->getSem(), aggs[i]->isOptim()));
	}

	bool unsat = false, sat = false;
	ca->initialize(unsat, sat);
	if(sat || unsat){
		delete ca;
	}
	return unsat;
}

void AggSolver::addSet(CalcAgg* ca){
	sets.push_back(ca);
	//Initialize network of body literals:
	for(vsize i=0; i<ca->getWL().size(); i++){
		network[var(ca->getWL()[i])].push_back(ca);
	}
}

bool AggSolver::constructMinSet(ppaset set, vppagg aggs){
	vwl wl;
	for(vsize i=0; i<set->getWL().size(); i++){
		wl.push_back(WL(set->getWL()[i], -set->getWL()[i]));
	}
	ppaset set2 = new ParsedSet(set->getID(), wl);
	vppagg aggs2;
	for(vsize i=0; i<aggs.size(); i++){
		ppagg agg = aggs[i];
		AggSign sign = agg->getSign()==LB?UB:LB;
		ppagg agg2 = new ParsedAgg(-agg->getBound(), sign, agg->getHead(), agg->getSem(), set2, agg->getType());
		aggs2.push_back(agg2);
	}

	bool unsat = constructMaxSet(set2, aggs2);
	delete set2;

	return unsat;
}

bool AggSolver::constructMaxSet(ppaset set, vppagg aggs){
	CalcAgg* ca = new MaxCalc(this, set->getWL());
	return initCalcAgg(ca, aggs);
}

bool AggSolver::constructCardSet(ppaset set, vppagg aggs){
	map<Var, bool> occurs;
	bool tosum = false;
	for(vsize i=0; !tosum && i<set->getWL().size(); i++){
		if(set->getWL()[i]!=1){
			tosum = true;
		}else if(occurs.find(var(set->getWL()[i]))!=occurs.end()){
			tosum = true;
		}else{
			occurs[var(set->getWL()[i])]=true;
		}
	}
	if(tosum){
		return constructSumSet(set, aggs);
	}

	//Card>=1 is translated away as an equivalence!
	vppagg checkedaggs;
	for(int i=0; i<aggs.size(); i++){
		ppagg agg = aggs[i];
		if(agg->getSign()==UB && agg->getBound()==1){
			//Can be translated straight to ONE clause!
			vec<Lit> right;
			for(int j=0; j<set->getWL().size(); j++){
				right.push(set->getWL()[j]);
			}
			if(agg->getSem()==DEF){
				if(!getPCSolver()->addRule(false, agg->getHead(), right)){
					return false;
				}
			}else if(!getPCSolver()->addEquivalence(agg->getHead(), right, false)){
				return false;
			}

		}else{
			checkedaggs.push_back(aggs[i]);
		}
	}

	if(getPCSolver()->modes().pw){ //use PWatches
		/* TODO if set reuse is supported, only split into two parts
		vppagg lower, higher;
		for(vsize i=0; i<aggs.size(); i++){
			if(aggs[i]->getSign()==LOWERBOUND){
				lower.push_back(aggs[i]);
			}else{
				higher.push_back(aggs[i]);
			}
		}
		CalcAgg* ca = new CardCalc(this, set->getWL());
		bool unsat  = initCalcAgg(ca, lower);
		CalcAgg* ca2 = new CardCalc(this, set->getWL());
		return !unsat || initCalcAgg(ca2, higher);*/

		//Currently, add each aggregate as a separate constraint
		bool unsat = false;
		for(vsize i=0; !unsat && i<checkedaggs.size(); i++){
			CalcAgg* ca = new CardCalc(this, set->getWL());
			vppagg aggs2;
			aggs2.push_back(checkedaggs[i]);
			unsat = initCalcAgg(ca, aggs2);
		}
		return unsat;
	}else{
		CalcAgg* ca = new CardCalc(this, set->getWL());
		return initCalcAgg(ca, checkedaggs);
	}
}

bool AggSolver::constructSumSet(ppaset set, vppagg aggs){
	//TODO only weights 1 and -1 should also be rewritten as a card!
	map<Var, bool> occurs;
	bool tocard = true;
	for(vsize i=0; tocard && i<set->getWL().size(); i++){
		if(set->getWL()[i]!=1){
			tocard = false;
		}else if(occurs.find(var(set->getWL()[i]))!=occurs.end()){
			tocard = false;
		}else{
			occurs[var(set->getWL()[i])]=true;
		}
	}
	if(tocard){
		return constructCardSet(set, aggs);
	}
	CalcAgg* ca = new SumCalc(this, set->getWL());
	return initCalcAgg(ca, aggs);
}

bool AggSolver::constructProdSet(ppaset set, vppagg aggs){
	for(vsize i=0; i<set->getWL().size(); i++){
		if(set->getWL()[i] < 1) { //Exception if product contains negative/zero weights
			char s[200];
			sprintf(s,
					"Error: Set nr. %d contains a 0 (zero) or negative weight %s, which cannot "
					"be used in combination with a product aggregate\n",
					set->getID(), printWeight(set->getWL()[i]).c_str());
			throw idpexception(s);
		}
	}

	CalcAgg* ca = new ProdCalc(this, set->getWL());
	return initCalcAgg(ca, aggs);
}

/**
 * The method propagates the fact that p has been derived to the SAT solver. If a conflict occurs,
 * a conflict clause is returned. Otherwise, the value is set to true in the sat solver.
 *
 * @pre: literal p can be derived to be true because of the given aggregate reason
 * @remarks: only method allowed to use the sat solver datastructures
 * @returns: non-owning pointer
 */
rClause AggSolver::notifySolver(AggReason* ar) {
	const Lit& p = ar->getPropLit();

	//FIXME decide on what to do with it
	//This strongly improves the performance of some benchmarks, e.g. FastFood. For Hanoi it has no effect
	//for Sokoban it DECREASES performance!
	//TODO new IDEA: mss nog meer afhankelijk van het AANTAL sets waar het in voorkomt of de grootte van de sets?
	//want de grootte van de set bepaalt hoe vaak de literal zou zijn uitgeschreven in een cnf theorie
	//getPCSolver()->varBumpActivity(var(p));

	if(value(p) != l_True && getPCSolver()->modes().aggclausesaving<2){
		vec<Lit> lits;
		lits.push(p);
		ar->getAgg().getAggComb()->getExplanation(lits, *ar);
		ar->setClause(lits);
	}

	if (value(p) == l_False) {
		if (verbosity() >= 2) {
			reportf("Deriving conflict in ");
			gprintLit(p, l_True);
			reportf(" because of the aggregate expression ");
			Aggrs::printAgg(ar->getAgg(), true);
		}
		assert(getPCSolver()->modes().aggclausesaving>1 || ar->hasClause());
		assert(aggreason[var(p)]==NULL || getPCSolver()->modes().aggclausesaving>1 || aggreason[var(p)]->hasClause());

		AggReason* old_ar = aggreason[var(p)];
		aggreason[var(p)] = ar;
		rClause confl = getExplanation(p);
		aggreason[var(p)] = old_ar;
		delete ar;	// Have to delete before addLearnedClause, as internally it might lead to backtrack and removing the reason
		getPCSolver()->addLearnedClause(confl);
		return confl;
	} else if (value(p) == l_Undef) {
		if (verbosity() >= 2) {
			reportf("Deriving ");
			gprintLit(p, l_True);
			reportf(" because of the aggregate expression ");
			Aggrs::printAgg(ar->getAgg(), true);
		}
		assert(aggreason[var(p)] == NULL);
		aggreason[var(p)] = ar;

		if(getPCSolver()->modes().aggclausesaving<1){
			rClause c = getPCSolver()->createClause(ar->getClause(), true);
			getPCSolver()->addLearnedClause(c);
		}

		getPCSolver()->setTrue(p, BYAGG);
	} else {
		delete ar;
	}
	return nullPtrClause;
}

void AggSolver::newDecisionLevel() {
	for(vsize i=0; i<sets.size(); i++){
		sets[i]->newDecisionLevel();
	}

	/*if(verbosity()>=6){
		reportf("Current effective watches on new decision level: \n");
		printWatches(this, tempwatches);
	}*/
}

void AggSolver::backtrackDecisionLevel(){
	for(vsize i=0; i<sets.size(); i++){
		sets[i]->backtrackDecisionLevel();
	}
}

/**
 * Returns non-owning pointer
 */
rClause AggSolver::propagate(const Lit& p) {
	if (!isInitialized()) {
		return nullPtrClause;
	}

	assert(assigns[var(p)]==l_Undef);
	assigns[var(p)] = sign(p)?l_False:l_True;

	rClause confl = nullPtrClause;

	if (verbosity() >= 2) {
		reportf("Aggr_propagate(");
		gprintLit(p, l_True);
		reportf(").\n");
	}

	/*if(verbosity()>=8){
		reportf("Current effective watches BEFORE: \n");
		printWatches(this, tempwatches);
	}*/

	pagg pa = headwatches[var(p)];
	if (pa != NULL) {
		confl = pa->getAggComb()->propagate(*pa);
		propagations++;
	}

	vector<pw>& ws = permwatches[var(p)];
	for (vector<pw>::const_iterator i = ws.begin(); confl == nullPtrClause && i
			< ws.end(); i++) {
		confl = (*i)->getAggComb()->propagate(p, *i);
		propagations++;
	}

	if (confl != nullPtrClause) {
		return confl;
	}

	vector<pw> ws2(tempwatches[toInt(p)]); //IMPORTANT, BECAUSE WATCHES MIGHT BE ADDED AGAIN TO THE END (if no other watches are found etc)
	tempwatches[toInt(p)].clear();

	vsize i = 0;
	for (; confl == nullPtrClause && i < ws2.size(); i++) {
		confl = ws2[i]->getAggComb()->propagate(p, ws2[i]);
		propagations++;
	}
	for (; i < ws2.size(); i++){
		addTempWatch(p, ws2[i]);
	}

	/*if(verbosity()>=8){
		reportf("Current effective watches AFTER: \n");
		printWatches(this, tempwatches);
	}*/

	return confl;
}

/**
 * Returns OWNING pointer. This has proven to be faster than always adding generated explanations to the
 * clause store!
 *
 * Important: verify that the clause is never constructed in and added to a different SAT-solvers!
 */
rClause AggSolver::getExplanation(const Lit& p) {
	assert(aggreason[var(p)] != NULL);
	const AggReason& ar = *aggreason[var(p)];

	rClause c = nullPtrClause;
	if(getPCSolver()->modes().aggclausesaving<2){
		assert(getPCSolver()->modes().aggclausesaving>0);
		assert(ar.hasClause());

		/*getPCSolver()->varBumpActivity(var(p));
		for(int i=0; i<ar.getClause().size(); i++){
			getPCSolver()->varBumpActivity(var(ar.getClause()[i]));
		}*/

		c = getPCSolver()->createClause(ar.getClause(), true);
	}else{
		//get the explanation from the aggregate expression
		vec<Lit> lits;
		lits.push(p);

		ar.getAgg().getAggComb()->getExplanation(lits, ar);

		/*getPCSolver()->varBumpActivity(var(p));
		for(int i=0; i<lits.size(); i++){
			getPCSolver()->varBumpActivity(var(lits[i]));
		}*/

		//create a conflict clause and return it
		c = getPCSolver()->createClause(lits, true);
	}

	//getPCSolver()->addLearnedClause(c); //Adding directly as a learned clause should NOT be done, only when used as direct conflict reason: real slowdown for magicseries

	return c;
}

/**
 * Not viable to backtrack a certain number of literals, unless also tracking whether a literal was propagated in
 * which solvers when a conflict occurred
 */
void AggSolver::backtrack(const Lit& l) {
	if (!isInitialized()) {
		return;
	}

	assigns[var(l)] = l_Undef;

	if (aggreason[var(l)] != NULL) {
		delete aggreason[var(l)];
		aggreason[var(l)] = NULL;
	}

	pagg pa = headwatches[var(l)];
	if (pa != NULL) {
		pa->getAggComb()->backtrack(*pa);
	}

	vector<pw>& vcw = permwatches[var(l)];
	for (vector<pw>::const_iterator i = vcw.begin(); i < vcw.end(); i++) {
		(*i)->getAggComb()->backtrack(**i);
	}
}

///////
// RECURSIVE AGGREGATES
///////

/**
 * For an aggregate expression defined by v, add all set literals to loopf that
 * 		have not been added already(seen[A]==1 for A, seen[A]==2 for ~A)
 * 		might help to make the expression true (monotone literals!)
 */
void AggSolver::addExternalLiterals(Var v, const std::set<Var>& ufs, vec<Lit>& loopf, vec<int>& seen) {
	const Agg& agg = *getAggWithHead(v);
	paggs comb = agg.getAggComb();

	for (vwl::const_iterator i = comb->getWL().begin(); i < comb->getWL().end(); ++i) {
		Lit l = (*i).getLit();
		if (comb->isMonotone(agg, *i) && ufs.find(var(l)) == ufs.end()
				&& seen[var(l)] != (isPositive(l) ? 2 : 1) && isFalse(l)) { //TODO deze laatste voorwaarde is een HACK: eigenlijk moeten de voorwaarden zo zijn, dat enkel relevant literals worden toegevoegd, maar momenteel worden er ook literals toegevoegd die nooit in een justification zullen zitten
			assert(isFalse(l));
			loopf.push(l);
			seen[var(l)] = isPositive(l) ? 2 : 1;
		}
		//TODO en neem er zoveel monotone niet zodat ze met de ufs erbij het agg nog true kunnen maken, maar zonder niet
	}
}

vector<Var> AggSolver::getAggHeadsWithBodyLit(Var x){
	vector<Var> heads;
	for(vector<paggs>::const_iterator i=network[x].begin(); i<network[x].end(); i++){
		for(vpagg::const_iterator j=(*i)->getAgg().begin(); j<(*i)->getAgg().end(); j++){
			heads.push_back(var((*j)->getHead()));
		}
	}
	return heads;
}

vwl::const_iterator AggSolver::getAggLiteralsBegin(Var x) const {
	return getAggWithHead(x)->getAggComb()->getWL().begin();
}

vwl::const_iterator AggSolver::getAggLiteralsEnd(Var x) const {
	return getAggWithHead(x)->getAggComb()->getWL().end();
}

/**
 * Propagates the fact that w has been justified and use the info on other earlier justifications to derive other
 * heads.
 *
 * @post: any new derived heads are in heads, with its respective justification in jstf
 */
void AggSolver::propagateJustifications(Lit w, vec<vec<Lit> >& jstfs, vec<Lit>& heads, vec<Var>& currentjust) {
	for (vector<paggs>::const_iterator i = network[var(w)].begin(); i< network[var(w)].end(); i++) {
		paggs s = (*i);
		for (vpagg::const_iterator j = s->getAgg().begin(); j < s->getAgg().end(); j++) {
			const Agg& expr = *(*j);
			if (isFalse(expr.getHead())) {
				//reportf(" => head is false %d\n", gprintVar(var(expr->getHead())));
				continue;
			}

			//WRONG WRONG
			//If not monotone, then the head can never become true by w
			//if(!expr->isMonotone((*(set->getWLBegin()+(*i).getIndex())))){
			//	reportf(" => occurence is not monotone in agg %d \n", gprintVar(var(expr->getHead())));
			//	continue;
			//}

			//reportf("=> checking agg %d \n", gprintVar(var(expr->getHead())));

			Var head = var(expr.getHead());
			if (currentjust[head] > 0) { //only check its body for justification when it has not yet been derived
				vec<Lit> jstf;
				vec<Var> nonjstf;
				if (s->canJustifyHead(expr, jstf, nonjstf, currentjust, false)) {
					currentjust[head] = 0;
					heads.push(mkLit(head, false));
					jstfs.push();
					jstf.copyTo(jstfs.last());
				}
			}
		}
	}
}

/**
 * The given head is not false. So it has a (possibly looping) justification. Find this justification
 */
void AggSolver::findJustificationAggr(Var head, vec<Lit>& outjstf) {
	vec<Var> nonjstf;
	vec<int> currentjust;
	const Agg& agg = *getAggWithHead(head);
	agg.getAggComb()->canJustifyHead(agg, outjstf, nonjstf, currentjust, true);
}

/**
 * Check whether the given var is justified by the current justification graph. If this is the case, jstf will
 * contain its justification and true will be returned. Otherwise, false will be returned and nonjstf will contain
 * all body literals of v that are not justified.
 */
bool AggSolver::directlyJustifiable(Var v, vec<Lit>& jstf, vec<Var>& nonjstf, vec<Var>& currentjust) {
	const Agg& agg = *getAggWithHead(v);
	return agg.getAggComb()->canJustifyHead(agg, jstf, nonjstf, currentjust, false);
}

///////
// OPTIMIZATION
///////

//FIXME no optimizations should take place on mnmz aggregates (partially helped by separate add method).
//FIXME 2 more optimization should/could take place on other aggregates
bool AggSolver::addMnmzSum(Var headv, int setid, AggSign boundsign) {
	if (parsedsets.find(setid)==parsedsets.end()) {
		char s[100];
		sprintf(s, "Set nr. %d is used, but not defined yet.\n", setid);
		throw idpexception(s);
	}

	assert(headv>=0);

	ppaset set = parsedsets[setid];

	// Check whether the head occurs in the body of the set, which is no longer allowed
	for(vsize i=0; i<set->getWL().size() ;i++){
		if(var(set->getWL()[i])==headv){ //Exception if head occurs in set itself
			char s[100];
			sprintf(s, "Set nr. %d contains a literal of atom %d, the head of an aggregate, which is not allowed.\n", setid, gprintVar(headv));
			throw idpexception(s);
		}
	}

	//Check that not aggregates occur with the same heads
	for(map<int, ppaset>::const_iterator i=parsedsets.begin(); i!=parsedsets.end(); i++){
		for(vsize j=0; j<(*i).second->getAgg().size(); j++){
			if(var((*i).second->getAgg()[j]->getHead())==headv){ //Exception if two agg with same head
				char s[100];
				sprintf(s, "At least two aggregates have the same head(%d).\n", gprintVar(headv));
				throw idpexception(s);
			}
		}
	}

	//the head of the aggregate
	Lit head = mkLit(headv, false);

	Weight max = 0, min = 0;
	for(vwl::const_iterator i=set->getWL().begin(); i<set->getWL().end(); i++){
		if((*i).getWeight()>0){
			max += (*i).getWeight();
		}else{
			min += (*i).getWeight();
		}
	}

	ppagg ae = new ParsedAgg(boundsign==LB ? max+1 : min, boundsign, head, COMP, set, SUM);
	ae->setOptim(); //FIXME temporary solution

	if (verbosity() >= 3) {
		reportf("Added sum minimization: Minimize ");
		//TODO
		//printAggrExpr(ae);
		reportf("\n");
	}

	return true;
}

bool AggSolver::invalidateSum(vec<Lit>& invalidation, Var head) {
	pagg a = headwatches[head];
	CalcAgg* s = a->getAggComb();
	SumFWAgg* prop = dynamic_cast<SumFWAgg*>(s->getProp());

	reportf("Current optimum: %s\n", printWeight(prop->getCC()).c_str());

	if (a->isLower()) {
		a->setLowerBound(prop->getCC() - 1);
	} else if (a->isUpper()) {
		a->setUpperBound(prop->getCC() - 1);
	}

	if (s->getBestPossible() == prop->getCC()) {
		return true;
	}

	prop->getMinimExplan(*a, invalidation);

	return false;
}

/**
 * FIXME: not really beautiful solution, maybe it can be fixed with ASSUMPTIONS?
 * This method has to be called after every temporary solution has been found to force the propagation of
 * the newly adapted bound.
 */
void AggSolver::propagateMnmz(Var head) {
	dynamic_cast<SumFWAgg*> (headwatches[head]->getAggComb()->getProp())->propagate(*headwatches[head], true);
}

///////
// PRINTING
///////

void AggSolver::printStatistics() const {
	reportf("aggregate propagations: %-12" PRIu64 "\n", propagations);
}

/*void AggSolver::findClausalPropagations(){
 int counter = 0;
 for(vsize i=0; i<aggrminsets.size(); i++){
 vector<Var> set;
 for(lwlv::const_iterator j=aggrminsets[i]->getWLBegin(); j<aggrminsets[i]->getWLEnd(); j++){
 set.push_back(var((*j).getLit()));
 }
 counter += getPCSolver()->getClausesWhichOnlyContain(set).size();
 }
 for(vsize i=0; i<aggrprodsets.size(); i++){
 vector<Var> set;
 for(lwlv::const_iterator j=aggrprodsets[i]->getWLBegin(); j<aggrprodsets[i]->getWLEnd(); j++){
 set.push_back(var((*j).getLit()));
 }
 counter += getPCSolver()->getClausesWhichOnlyContain(set).size();
 }
 for(vsize i=0; i<aggrsumsets.size(); i++){
 vector<Var> set;
 for(lwlv::const_iterator j=aggrsumsets[i]->getWLBegin(); j<aggrsumsets[i]->getWLEnd(); j++){
 set.push_back(var((*j).getLit()));
 }
 counter += getPCSolver()->getClausesWhichOnlyContain(set).size();
 }
 for(vsize i=0; i<aggrmaxsets.size(); i++){
 vector<Var> set;
 for(lwlv::const_iterator j=aggrmaxsets[i]->getWLBegin(); j<aggrmaxsets[i]->getWLEnd(); j++){
 set.push_back(var((*j).getLit()));
 }
 counter += getPCSolver()->getClausesWhichOnlyContain(set).size();
 }
 reportf("Relevant clauses: %d.\n", counter);
 }*/
