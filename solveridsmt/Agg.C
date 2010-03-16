#include "Agg.h"
#include "AggSolver.h"
#include <algorithm>

void AggrSet::backtrack(int index) {
	//BELANGRIJK: hier had ik een referentie gezet en dan deed ik pop, wat dus niet mag, want dan is die value kwijt!
	PropagationInfo pi = stack.back();
	stack.pop_back();

	assert(pi.getType()!=HEAD && var(pi.getLit())==var(wlits[index].getLit()));

	wlits[index].setValue(l_Undef);
	setCC(pi.getPC());
	setCP(pi.getPP());
}

Clause* AggrSet::propagate(const Lit& p, const AggrWatch& ws){
	Occurrence tp;
    if (ws.getType()==POS){
    	tp = sign(p)? NEG : POS;
    }else{
    	tp = sign(p)? POS : NEG;
    }

	stack.push_back(PropagationInfo(p, wlits[ws.getIndex()].getWeight(),tp, getCC(), getCP()));

	wlits[ws.getIndex()].setValue(tp==POS?l_True:l_False);

	tp==POS? addToCertainSet(wlits[ws.getIndex()]):removeFromPossibleSet(wlits[ws.getIndex()]);

	return propagateBodies();
}

Clause* AggrSet::propagateBodies(){
	Clause* confl = NULL;
	for(lwagg::const_iterator i=getAggBegin(); i<getAggEnd() && confl==NULL; i++){
		pAgg pa = (*i).lock();
		lbool hv = pa->getHeadValue();
		if(hv != l_Undef){ //head is already known
			lbool result = pa->canPropagateHead();
			if(result!=l_Undef && result!=hv){
				//conflict!
				confl = AggSolver::aggsolver->notifySATsolverOfPropagation(result==l_True?pa->getHead():~pa->getHead(), new AggrReason(*i, pa->getHeadIndex()));
			}else{
				confl = pa->propagate(hv==l_True);
			}
		}else{ //head is not yet known, so at most the head can be propagated
			lbool result = pa->canPropagateHead();
			if(result!=l_Undef){
				confl = AggSolver::aggsolver->notifySATsolverOfPropagation(result==l_True?pa->getHead():~pa->getHead(), new AggrReason(*i, pa->getHeadIndex()));
			}
		}
	}
	return confl;
}

/*
 * To be able to handle multiple times the same literal and also its negation, we will be checking here if the set conforms to that
 * If it does not, a duplicate will be created, which will only be used in this aggregate and which conforms to the rules
 */
bool compareLits(const WLit& one, const WLit& two) {
	return var(one.getLit())<var(two.getLit());
}

/**
 * Checks whether the same literal occurs multiple times in the set
 * If this is the case, all identical literals are combined into one.
 *
 * @post: the literals are sorted according to weight again
 */
void AggrSet::doSetReduction() {
	lwlv& oldset = wlits;
	lwlv newset;

	//Sort all wlits according to the integer representation of their literal (to get all literals next to each other)
	std::sort(oldset.begin(), oldset.end(), compareLits);

	int indexinnew = 0;
	newset.push_back(oldset[indexinnew]);

	bool setisreduced = false;
	for(lwlv::size_type i=1; i<oldset.size(); i++){
		WLV oldl = newset[indexinnew];
		WLV newl = oldset[i];
		if(var(oldl.getLit())==var(newl.getLit())){ //same variable
			setisreduced = true;
			if(oldl.getLit()==newl.getLit()){ //same literal, keep combined weight
				Weight w = getCombinedWeight(newl.getWeight(), oldl.getWeight());
				newset[indexinnew] = WLV(oldl.getLit(), w, oldl.getValue());
			}else{ //opposite signs
				WLit wl = handleOccurenceOfBothSigns(oldl, newl);
				newset[indexinnew] = WLV(wl.getLit(), wl.getWeight(), oldl.getValue());
			}
		}else{
			newset.push_back(newl);
			indexinnew++;
		}
	}

	if(setisreduced){
		wlits.clear();
		wlits.insert(wlits.begin(), newset.begin(), newset.end());
	}

	//important to sort again to guarantee that it is sorted according to the weights
	std::sort(wlits.begin(), wlits.end());
}

void AggrSet::initialize(){
	initEmptySetValue(); //important to do first!
	doSetReduction();
	setCP(getBestPossible());
	setCC(getEmptySetValue());
}

/*******
 * AGG *
 *******/

void Agg::backtrackHead(){
	headvalue = l_Undef;
	headindex = -1;
}

Clause* Agg::propagateHead(const Lit& p){
	bool headtrue = head==p;
	headvalue = headtrue?l_True:l_False;
	headindex = set.lock()->getStackSize();
	return propagateHead(headtrue);
}

/*****************
 * MAX AGGREGATE *
 *****************/

Weight AggrMaxSet::getBestPossible() const{
	return wlits.back().getWeight();
}

void AggrMaxSet::initEmptySetValue(){
	//FIXME FIXME: moet eigenlijk een voorstelling van -infinity zijn
	//ik had eerst: minimum van de set -1, maar de bound kan NOG lager liggen, dus dan is het fout
	setEmptySetValue(Weight(-400000000));
}

void AggrMaxSet::addToCertainSet(const WLit& l){
	if(l.getWeight()>getCC()){
		setCC(l.getWeight());
	}
}

void AggrMaxSet::removeFromPossibleSet(const WLit& l){
	if(l.getWeight()==getCP()){
		bool found = false;
		for(lwlv::reverse_iterator i=wlits.rbegin(); !found && i<wlits.rend(); i++){
			if((*i).getValue() != l_False){
				setCP((*i).getWeight());
				found = true;
			}
		}
		if(!found){
			setCP(getEmptySetValue());
		}
	}
}

Weight	AggrMaxSet::getCombinedWeight(const Weight& first, const Weight& second) const{
	return first>second?first:second;
}

WLit AggrMaxSet::handleOccurenceOfBothSigns(const WLit& one, const WLit& two){
	if(one.getWeight()>two.getWeight()){
		if(getEmptySetValue()<two.getWeight()){
			setEmptySetValue(two.getWeight());
		}
		return one;
	}else{
		if(getEmptySetValue()<one.getWeight()){
			setEmptySetValue(one.getWeight());
		}
		return two;
	}
}

lbool Agg::canPropagateHead() const{
	pSet s = set.lock();
	if ((lower && s->getCC() > bound) || (!lower && s->getCP() < bound)) {
		return l_False;
	} else if ((lower && s->getCP() <= bound) || (!lower && s->getCC() >= bound)) {
		return l_True;
	} else {
		return l_Undef;
	}
}

/**
 * head is true  && AGG <= B:
 * 		make all literals false with weight larger than bound
 * head is false && A <= AGG:
 * 		make all literals false with weight larger/eq than bound
 */
Clause* MaxAgg::propagateHead(bool headtrue) {
	pSet s = set.lock();
	Clause* confl = NULL;
	if (headtrue && lower) {
		lwlv::const_reverse_iterator i=s->getWLRBegin();
		while( confl == NULL && i<s->getWLREnd() && bound<(*i).getWeight()){
			confl = AggSolver::aggsolver->notifySATsolverOfPropagation(~(*i).getLit(), new AggrReason(getAgg(), s->getStackSize()));
			i++;
		}
	}else if(!headtrue && !lower){
		lwlv::const_reverse_iterator i=s->getWLRBegin();
		while( confl == NULL && i<s->getWLREnd() && bound<=(*i).getWeight()){
			confl = AggSolver::aggsolver->notifySATsolverOfPropagation(~(*i).getLit(), new AggrReason(getAgg(), s->getStackSize()));
			i++;
		}
	}
	if(confl==NULL){
		confl = propagate(headtrue);
	}
	return confl;
}

/**
 * If only one value is still possible and the head has already been derived, then this last literal
 * might also be propagated, if the constraint is NOT YET SATISFIED!!!
 *
 * head is true  && A <= AGG: Last literal has to be true
 * head is true  && AGG <= B: No conclusion possible (emptyset is also a solution)
 * head is false && A <= AGG: No conclusion possible (emptyset is also a solution)
 * head is false && AGG <= B: Last literal has to be true
 */
Clause* MaxAgg::propagate(bool headtrue) {
	Clause* confl = NULL;
	if((lower && headtrue) || (!lower && !headtrue)){
		return confl;
	}
	pSet s = set.lock();
	lwlv::const_iterator pos = s->getWLEnd();
	bool exactlyoneleft = true;
	for(lwlv::const_iterator i=s->getWLBegin(); exactlyoneleft && i<s->getWLEnd(); i++){
		if((!lower && headtrue && (*i).getWeight()>=bound) || (lower && !headtrue && (*i).getWeight()>bound)){
			if((*i).getValue()==l_Undef){
				if(pos!=s->getWLEnd()){
					exactlyoneleft = false;
				}else{
					pos = i;
				}
			}else if((*i).getValue()==l_True){
				exactlyoneleft = false;
			}
		}
	}
	if(exactlyoneleft){
		confl = AggSolver::aggsolver->notifySATsolverOfPropagation((*pos).getLit(), new AggrReason(getAgg(), s->getStackSize()));
	}
	return confl;
}

/*****************
 * SUM AGGREGATE *
 *****************/

Weight	AggrSumSet::add(const Weight& lhs, const Weight& rhs) const{
	return lhs+rhs;
}
Weight	AggrSumSet::remove(const Weight& lhs, const Weight& rhs) const{
	return lhs-rhs;
}
Weight	AggrProdSet::add(const Weight& lhs, const Weight& rhs) const{
	return lhs*rhs;
}
Weight	AggrProdSet::remove(const Weight& lhs, const Weight& rhs) const{
	return rhs==0?0:lhs/rhs;
}
Weight	SumAgg::add(const Weight& lhs, const Weight& rhs) const{
	return lhs+rhs;
}
Weight	SumAgg::remove(const Weight& lhs, const Weight& rhs) const{
	return lhs-rhs;
}
Weight	ProdAgg::add(const Weight& lhs, const Weight& rhs) const{
	return lhs*rhs;
}
Weight	ProdAgg::remove(const Weight& lhs, const Weight& rhs) const{
	return rhs==0?0:lhs/rhs;
}

void AggrSumSet::initEmptySetValue(){
	setEmptySetValue(Weight(0));
}

WLit AggrSumSet::handleOccurenceOfBothSigns(const WLit& one, const WLit& two){
	if(one.getWeight()<two.getWeight()){
		setEmptySetValue(getEmptySetValue() + one.getWeight());
		return WLit(two.getLit(), this->remove(two.getWeight(), one.getWeight()));
	}else{
		setEmptySetValue(getEmptySetValue() + two.getWeight());
		return WLit(one.getLit(), this->remove(one.getWeight(), two.getWeight()));
	}
}

/*********************
 * PRODUCT AGGREGATE *
 *********************/

Weight AggrSPSet::getBestPossible() const{
	Weight max = getEmptySetValue();
	for (lwlv::const_iterator j = wlits.begin(); j < wlits.end(); j++) {
		max = this->add(max, (*j).getWeight());
	}
	return max;
}

void AggrSPSet::addToCertainSet(const WLit& l){
	setCC(this->add(getCC(), l.getWeight()));
}

void AggrSPSet::removeFromPossibleSet(const WLit& l){
	setCP(this->remove(getCP(), l.getWeight()));
}

void AggrProdSet::initEmptySetValue(){
	setEmptySetValue(Weight(1));
}

/**
 * multi-set semantics!
 */
Weight	AggrSPSet::getCombinedWeight(const Weight& first, const Weight& second) const{
	return this->add(first, second);
}

WLit AggrProdSet::handleOccurenceOfBothSigns(const WLit& one, const WLit& two){
	//NOTE: om dit toe te laten, ofwel bij elke operatie op en literal al zijn voorkomens overlopen
	//ofwel aggregaten voor doubles ondersteunen (het eerste is eigenlijk de beste oplossing)
	//Mogelijke eenvoudige implementatie: weigts bijhouden als doubles (en al de rest als ints)
	reportf("Product aggregates in which both the literal and its negation occur "
			"are currently not supported. Replace ");
	gprintLit(one.getLit());
	reportf("or ");
	gprintLit(two.getLit());
	reportf("by a tseitin.\n");
	exit(3);
}

/**
 * If head is true, and making a literal true would increase the bestcertain value above the bound (and lEQ)
 * 					or  making a literal false would decrease the bestpossible below the bound (and gEQ)
 * 		then make that literal and all higher ones (in weight) false (resp. true)
 *
 * If head is false, and making a literal false would decrease the bestcertain below the bound (and lEQ)
 * 					 or making a literal true would increase the bestpossible above the bound (and gEQ)
 * 		then make that literal and all higher ones (in weight) true (resp. false)
 *
 * Only unknown literals are checked! The other literals will already have been included in the bounds, so using them is wrong (and not useful)
 *
 * IMPORTANT: smart use of the fact that all literals in the set are ordered according to the weight:
 * 		if !lower and substracting from bestpossible gets below the bound, then all literals with that weight and higher should be false
 * 		if lower and adding to bestcertain gets above the bound, then all literals with that weight and higher should be false
 * this is done using the lower_bound binary search algorithm of std
 */
Clause* SPAgg::propagateHead(bool headtrue){
	return propagate(headtrue);
}

Clause* SPAgg::propagate(bool headtrue){
	Clause* c = NULL;
	Weight weightbound(0);
	pSet s = set.lock();

	//determine the lower bound of which weight literals to consider
	if (headtrue) {
		if(lower){
			weightbound = this->remove(bound, s->getCC());
			//+1 because larger and not eq
			weightbound+=1;
		}else{
			weightbound = this->remove(s->getCP(), bound);
			//+1 because larger and not eq
			weightbound+=1;
		}
	} else {
		if(lower){
			weightbound = this->remove(s->getCP(), bound);
		}else{
			weightbound = this->remove(bound, s->getCC());
		}
	}
	lwlv::const_iterator pos = lower_bound(s->getWLBegin(), s->getWLEnd(), weightbound);
	if(pos==s->getWLEnd()){
		return c;
	}

	//find the index of the literal
	int start = 0;
	lwlv::const_iterator it = s->getWLBegin();
	while(it!=pos){
		it++; start++;
	}

	for (lwlv::const_iterator u = s->getWLBegin()+start; c==NULL && u < s->getWLEnd(); u++) {
		if ((*u).getValue()==l_Undef) {//if already propagated as an aggregate, then those best-values have already been adapted
			if((lower && headtrue) || (!lower && !headtrue)){
				//assert((headtrue && set->currentbestcertain+set->wlits[u].weight>bound) || (!headtrue && set->currentbestcertain+set->wlits[u].weight>=bound));
				c = AggSolver::aggsolver->notifySATsolverOfPropagation(~(*u).getLit(), new AggrReason(getAgg(), s->getStackSize()));
			}else{
				//assert((!headtrue && set->currentbestpossible-set->wlits[u].weight<=bound) || (headtrue && set->currentbestpossible-set->wlits[u].weight<bound));
				c = AggSolver::aggsolver->notifySATsolverOfPropagation((*u).getLit(), new AggrReason(getAgg(), s->getStackSize()));
			}
		}
	}
	return c;
}

/*******************
 * CLAUSE LEARNING *
 *******************/

void Agg::getExplanation(vec<Lit>& lits, AggrReason& ar) const{
	assert(ar.getAgg().get() == this);

	if(ar.getIndex() >= headindex){
		//the head literal is saved as it occurred in the theory, so adapt for its current truth value!
		lits.push(headvalue==l_True?~head:head);
	}

	int counter = 0;
	pSet s = set.lock();
	for(lprop::const_iterator i=s->getStackBegin(); counter<ar.getIndex() && i<s->getStackEnd(); i++,counter++){
		lits.push(~(*i).getLit());
	}
}

void SumAgg::getMinimExplan(vec<Lit>& lits){
	pSet s = set.lock();
	Weight certainsum = s->getEmptySetValue();
	Weight possiblesum = s->getBestPossible();

	bool explained = false;
	if((lower && certainsum>bound) || (!lower && certainsum>=bound) || (lower && possiblesum <= bound) || (!lower && possiblesum < bound)){
		explained = true;
	}

	for(lprop::const_iterator i=s->getStackBegin(); !explained && i<s->getStackEnd(); i++){
		bool push = false;
		if((*i).getType() == POS){ //means that the literal in the set became true
			certainsum += (*i).getWeight();

			if(lower){
				push = true;
				if(bound < certainsum){
					explained = true;
				}
			}
		}else if((*i).getType() == NEG){ //the literal in the set became false
			possiblesum -= (*i).getWeight();

			if(!lower){
				push = true;
				if(possiblesum < bound){
					explained = true;
				}
			}
		}
		if(push){
			lits.push(~(*i).getLit());
		}
	}

	assert(explained);
}

/************************
 * RECURSIVE AGGREGATES *
 ************************/

/**
 * Important: to justify a head, often several body literals have to become FALSE
 * For such literals, they have to be justified if they are NEGATIVE
 *
 * Also, if a literal has to become FALSE, its INVERSION should be added to the justification!
 */

inline bool AggrSet::oppositeIsJustified(const WLV& elem, vec<int>& currentjust, bool real) const{
	if(real){
		return elem.getValue()!=l_True;
	}else{
		return elem.getValue()!=l_True && (!sign(elem.getLit()) || isJustified(var(elem.getLit()), currentjust));
	}
}
inline bool AggrSet::isJustified(const WLV& elem, vec<int>& currentjust, bool real) const{
	if(real){
		return elem.getValue()!=l_False;
	}else{
		return elem.getValue()!=l_False && (sign(elem.getLit()) || isJustified(var(elem.getLit()), currentjust));
	}
}
inline bool AggrSet::isJustified(Var x, vec<int>& currentjust) const{
	return currentjust[x]==0;
}

/**
 * Finds a new justification.
 * @pre: head is not false, so a justification exists
 */
void Agg::becomesCycleSource(vec<Lit>& j) const {
	assert(headvalue!=l_False);
	vec<Var> nonj;
	vec<int> s;
	bool justified = canJustifyHead(j, nonj, s, true);
	assert(justified);
	assert(j.size()>0); //v is not false, so a justification exists
}

/**
 * Add all literals that could make the head true and are not in the unfounded set to the loopformula
 */
void MaxAgg::createLoopFormula(const std::set<Var>& ufs, vec<Lit>& loopf, vec<int>& seen) const{
	pSet s = set.lock();
	if(lower){
		for (lwlv::const_reverse_iterator i=s->getWLRBegin(); i<s->getWLREnd() && (*i).getWeight()>bound; i++) {
			const Lit& l = (*i).getLit();
			if (l!=head && ufs.find(var(l)) == ufs.end() && seen[var(l)] != (sign(l) ? 2 : 1)) {
				loopf.push(~l);
				seen[var(l)] = (sign(l) ? 2 : 1);
			}
		}
	}else{
		for (lwlv::const_reverse_iterator i=s->getWLRBegin(); i<s->getWLREnd() && (*i).getWeight()>=bound; i++) {
			const Lit l = (*i).getLit();
			if (l!=head &&  ufs.find(var(l)) == ufs.end() && seen[var(l)] != (sign(l) ? 1 : 2)) {
				loopf.push(l);
				seen[var(l)] = (sign(l) ? 1 : 2);
			}
		}
	}
}

/**
 * IMPORTANT: comments from justifyHead for a minimum aggregate, has not yet been adapted.
 * AGG <= B: v is justified if one literal below/eq the bound is THAT IS NOT THE HEAD
 * 					if so, change the justification to the literal
 * 					otherwise, add all nonfalse, non-justified, relevant, below the bound literals to the queue
 * A <= AGG: v is justified if the negation of all literals below the bound are. The emptyset is always a solution,
 * 			 so no conclusions have to be drawn from the literals above/eq the bound
 * 					if so, change the justification to the negation of all those below the bound literals
 * 					otherwise, add all nonfalse, non-justified, relevant, below the bound literals to the queue
 * NOTE it might be possible to write this more efficiently, for some ideas see commits before 26/01/2010
 */
bool MaxAgg::canJustifyHead(vec<Lit>& jstf, vec<Var>& nonjstf, vec<int>& currentjust, bool real) const {
	bool justified = false;
	pSet s = set.lock();
	if(lower){
		for(lwlv::const_reverse_iterator i=s->getWLRBegin(); i<s->getWLREnd() && (*i).getWeight()>bound; i++) {
			if(s->oppositeIsJustified(*i, currentjust, real)){
				jstf.push(~(*i).getLit()); //push negative literal, because it should become false
			}else if(real ||currentjust[var((*i).getLit())]!=0){
				nonjstf.push(var((*i).getLit()));
			}
		}
		if(nonjstf.size()==0){
			justified = true;
		}
	}else{
		for(lwlv::const_reverse_iterator i=s->getWLRBegin(); i<s->getWLREnd() && (*i).getWeight()>=bound; i++) {
			if(s->isJustified(*i, currentjust, real)){
				jstf.push((*i).getLit());
				justified = true;
			}else if(real || currentjust[var((*i).getLit())]!=0){
				nonjstf.push(var((*i).getLit()));
			}
		}
	}
	if (!justified) {
		jstf.clear();
	}
	return justified;
}

/**
 * Idee is dat alle literals worden toegevoegd die (onafhankelijk van hun weight) mogelijk de head
 * waar kunnen maken. Dus als al die literals false worden, kan de head zeker op geen andere manier nog
 * waar worden dan door de ufs.
 */
void SPAgg::createLoopFormula(const std::set<Var>& ufs, vec<Lit>& loopf, vec<int>& seen) const{
	int f = lower?1:2;
	int s = lower?2:1;

	pSet pset = set.lock();
	for (lwlv::const_iterator i = pset->getWLBegin(); i < pset->getWLEnd(); ++i) {
		const Lit& l = (*i).getLit();
		if (l!=head && ufs.find(var(l)) == ufs.end() && seen[var(l)] != (sign(l) ? f : s)) {
			loopf.push(lower?~l:l);
			seen[var(l)] = (sign(l) ? f : s);
		}
	}
}

/**
 * AGG <= B: add a number of justified literals such that they guarantee the bestpossible value is below the bound
 * A <= AGG: need a justification of which the sum exceed/eq the bound
 */
bool SPAgg::canJustifyHead(vec<Lit>& jstf, vec<Var>& nonjstf, vec<int>& currentjust, bool real) const {
	bool justified = false;
	pSet s = set.lock();

	if(lower){
		Weight bestpossible = s->getBestPossible();
		for (lwlv::const_iterator i = s->getWLBegin(); !justified && i < s->getWLEnd(); ++i) {
			if(s->oppositeIsJustified(*i, currentjust, real)){
				jstf.push(~(*i).getLit());
				bestpossible = this->remove(bestpossible, (*i).getWeight());
				if (bestpossible <= bound){
					justified = true;
				}
			}else if(real ||currentjust[var((*i).getLit())]!=0){
				nonjstf.push(var((*i).getLit()));
			}
		}
	}else{
		Weight bestcertain = s->getEmptySetValue();
		for (lwlv::const_iterator i = s->getWLBegin(); !justified && i < s->getWLEnd(); ++i) {
			if(s->isJustified(*i, currentjust, real)){
				jstf.push((*i).getLit());
				bestcertain = this->add(bestcertain, (*i).getWeight());
				if (bestcertain >= bound){
					justified = true;
				}
			}else if(real ||currentjust[var((*i).getLit())]!=0){
				nonjstf.push(var((*i).getLit()));
			}
		}
	}
	return justified;
}
