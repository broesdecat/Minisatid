#include "Agg.h"
#include "AggSolver.h"
#include <algorithm>

//NOTE never use a decrementing vector iterator unless minding the 0 problem!!! (it is unsigned, so checking that
//the number is still positive is wrong!

void AggrSet::backtrack(int index) {
	PropagationInfo pi = stack.last();
	stack.pop();

	assert(pi.type!=HEAD && var(pi.wlit.lit)==var(wlitset[index].lit));

	litvalue[index] = l_Undef;
	if (pi.type == POS) {
		removeFromCertainSet(pi.wlit);
	}else{
		addToPossibleSet(pi.wlit);
	}
}

Clause* AggrSet::propagate(Lit p, AggrWatch& ws){
	Clause* confl = NULL;

	Occurrence tp = relativeOccurrence(ws.type, p);
	assert(tp!=HEAD);
	stack.push(PropagationInfo(p, wlitset[ws.index].weight,tp));

	if (tp == HEAD){
		assert(false);
	}else { // It's a set literal.
		litvalue[ws.index] = tp==POS?l_True:l_False;
		tp==POS? addToCertainSet(wlitset[ws.index]):removeFromPossibleSet(wlitset[ws.index]);

		confl = propagateBodies();
	}

	return confl;
}

Clause* AggrSet::propagateBodies(){
	Clause* confl = NULL;
	for(vector<Agg*>::iterator i=aggregates.begin(); i!=aggregates.end() && confl==NULL; i++){
		lbool result = (*i)->canPropagateHead();
		if(result==l_True){
			confl = AggSolver::aggsolver->notifySATsolverOfPropagation((*i)->head, new AggrReason(*i, HEAD, -1));
		}else if(result==l_False){
			confl = AggSolver::aggsolver->notifySATsolverOfPropagation(~(*i)->head, new AggrReason(*i, HEAD, -1));
		}else if((*i)->headvalue != l_Undef){ //the head cannot be directly propagated, but its value has already been found
			confl = (*i)->propagate((*i)->headvalue==l_True);
		}
	}
	return confl;
}

/*
 * To be able to handle multiple times the same literal and also its negation, we will be checking here if the set conforms to that
 * If it does not, a duplicate will be created, which will only be used in this aggregate and which conforms to the rules
 */
bool compareLits(WLit one, WLit two) { return var(one.lit)<var(two.lit); }

/**
 * Checks whether the same literal occurs multiple times in the set
 * If this is the case, all identical literals are combined into one.
 *
 * @post: the literals are sorted according to weight again
 */
void AggrSet::doSetReduction() {
	vector<WLit> oldset = wlitset, newset;

	//Sort all wlits according to the integer representation of their literal (to get all literals next to each other)
	std::sort(oldset.begin(), oldset.end(), compareLits);

	int indexinnew = 0;
	newset.push_back(oldset[indexinnew]);

	bool setisreduced = false;
	for(vector<int>::size_type i=1; i<oldset.size(); i++){
		WLit oldl = newset[indexinnew];
		WLit newl = oldset[i];
		if(var(oldl.lit)==var(newl.lit)){ //same variable
			setisreduced = true;
			if(oldl.lit==newl.lit){ //same literal, keep combined weight
				newset[indexinnew].weight = getCombinedWeight(newl.weight, oldl.weight);
			}else{ //opposite signs
				newset[indexinnew] = handleOccurenceOfBothSigns(oldl, newl);
			}
		}else{
			newset.push_back(newl);
			indexinnew++;
		}
	}

	//important to sort again to guarantee that it is sorted according to the weights
	std::sort(newset.begin(), newset.end());

	if(setisreduced){
		wlitset.clear();
		wlitset.insert(wlitset.begin(), newset.begin(), newset.end());
	}
}

void AggrSet::initialize(){
	doSetReduction();
	litvalue.growTo(wlitset.size(), l_Undef); //only initialize after setreduction!

	currentbestpossible = getBestPossible();
	currentbestcertain = emptysetValue;
	possiblecount = wlitset.size();
}

/*****************
 * MIN AGGREGATE *
 *****************/

int AggrMinSet::getBestPossible() {
	int min = emptysetValue;
	for (vector<Lit>::size_type j = 0; j < wlitset.size(); j++) {
		if(min > wlitset[j].weight){
			min = wlitset[j].weight;
		}
	}
	return min;
}

void AggrMinSet::removeFromCertainSet(WLit l){
	truecount--;
	if (truecount == 0) {
		currentbestcertain = emptysetValue;
	}else{
		if(l.weight==currentbestcertain){
			currentbestcertain = emptysetValue;
			for(int i=0; i<stack.size(); i++){
				if(stack[i].type==POS && stack[i].wlit.weight<currentbestcertain){
					currentbestcertain = stack[i].wlit.weight;
				}
			}
		}
	}
}

void AggrMinSet::addToCertainSet(WLit l){
	truecount++;
	if(l.weight<currentbestcertain){
		currentbestcertain = l.weight;
	}
}

void AggrMinSet::addToPossibleSet(WLit l){
	possiblecount++;
	if(l.weight<currentbestpossible){
		currentbestpossible = l.weight;
	}
}

void AggrMinSet::removeFromPossibleSet(WLit l){
	possiblecount--;
	if(possiblecount==0){
		currentbestpossible = emptysetValue;
	}else{
		if(l.weight==currentbestpossible){
			currentbestpossible = emptysetValue;
			for(vector<Lit>::size_type i=0; i<wlitset.size(); i++){
				if(litvalue[i] != l_False && wlitset[i].weight<currentbestpossible){
					currentbestpossible = wlitset[i].weight;
				}
			}
		}
	}
}

int	AggrMinSet::getCombinedWeight(int first, int second){
	return first<second?first:second;
}

WLit AggrMinSet::handleOccurenceOfBothSigns(WLit one, WLit two){
	if(one.weight<two.weight){
		if(emptysetValue>two.weight){
			emptysetValue = two.weight;
		}
		return one;
	}else{
		if(emptysetValue>one.weight){
			emptysetValue = one.weight;
		}
		return two;
	}
}

/*******
 * AGG *
 *******/

void Agg::backtrackHead(){
	headvalue = l_Undef;
	headindex = -1;
}

Clause* Agg::propagateHead(Lit p){
	bool headtrue = head==p;
	headvalue = headtrue?l_True:l_False;
	headindex = set->stack.size();
	return propagateHead(headtrue);
}

lbool MinAgg::canPropagateHead() {
	if ((lower && set->currentbestpossible > bound) || (!lower && set->currentbestcertain < bound)) {
		return l_False;
	} else if ((lower && set->currentbestcertain <= bound) || (!lower && set->currentbestpossible >= bound)) {
		return l_True;
	} else {
		return l_Undef;
	}
}

/**
 * head is true  && A <= AGG:
 * 		make all literals false with weight smaller than bound
 * head is false && AGG <= B:
 * 		make all literals false with weight smaller/eq than bound
 */
Clause* MinAgg::propagateHead(bool headtrue) {
	Clause* confl = NULL;
	if (headtrue && !lower) {
		vector<int>::size_type i=0;
		while( confl == NULL && i<set->wlitset.size() && set->wlitset[i].weight<bound){
			confl = AggSolver::aggsolver->notifySATsolverOfPropagation(~set->wlitset[i].lit, new AggrReason(this, NEG, i));
			i++;
		}
	}else if(!headtrue && lower){
		vector<int>::size_type i=0;
		while( confl == NULL && i<set->wlitset.size() && set->wlitset[i].weight<=bound){
			confl = AggSolver::aggsolver->notifySATsolverOfPropagation(~set->wlitset[i].lit, new AggrReason(this, NEG, i));
			i++;
		}
	}
	return confl;
}

/**
 * If only one value is still possible and the head has already been derived, then this last literal
 * might also be propagated
 *
 * head is true  && A <= AGG: No conclusion possible (emptyset is also a solution)
 * head is true  && AGG <= B: Last literal has to be true
 * head is false && A <= AGG: Last literal has to be true
 * head is false && AGG <= B: No conclusion possible (emptyset is also a solution)
 */
Clause* MinAgg::propagate(bool headtrue) {
	Clause* confl = NULL;
	if(set->possiblecount==1 && ((headtrue && lower) || (!headtrue && !lower))){
		for(vector<WLit>::size_type i=0; i<set->wlitset.size(); i++){
			if(set->litvalue[i]==l_Undef){
				confl = AggSolver::aggsolver->notifySATsolverOfPropagation(set->wlitset[i].lit, new AggrReason(this, POS, i));
				break;
			}
		}
	}
	return confl;
}

/*****************
 * MAX AGGREGATE *
 *****************/

int AggrMaxSet::getBestPossible() {
	int max = emptysetValue;

	for (vector<Lit>::size_type j = 0; j < wlitset.size(); j++) {
		if(max < wlitset[j].weight){
			max = wlitset[j].weight;
		}
	}
	return max;
}

void AggrMaxSet::removeFromCertainSet(WLit l){
	truecount--;
	if (truecount == 0) {
		currentbestcertain = emptysetValue;
	}else{
		if(l.weight==currentbestcertain){
			currentbestcertain = emptysetValue;
			for(int i=0; i<stack.size(); i++){
				if(stack[i].type==POS && currentbestcertain<stack[i].wlit.weight){
					currentbestcertain = stack[i].wlit.weight;
				}
			}
		}
	}
}

void AggrMaxSet::addToCertainSet(WLit l){
	truecount++;
	if(l.weight>currentbestcertain){
		currentbestcertain = l.weight;
	}
}

void AggrMaxSet::addToPossibleSet(WLit l){
	possiblecount++;
	if(l.weight>currentbestpossible){
		currentbestpossible = l.weight;
	}
}

void AggrMaxSet::removeFromPossibleSet(WLit l){
	possiblecount--;
	if(possiblecount==0){
		currentbestpossible = emptysetValue;
	}else{
		if(l.weight==currentbestpossible){
			currentbestpossible = emptysetValue;
			for(vector<Lit>::size_type i=0; i<wlitset.size(); i++){
				if(litvalue[i] != l_False && currentbestpossible < wlitset[i].weight){
					currentbestpossible = wlitset[i].weight;
				}
			}
		}
	}
}

int	AggrMaxSet::getCombinedWeight(int first, int second){
	return first>second?first:second;
}

WLit AggrMaxSet::handleOccurenceOfBothSigns(WLit one, WLit two){
	if(one.weight>two.weight){
		if(emptysetValue<two.weight){
			emptysetValue = two.weight;
		}
		return one;
	}else{
		if(emptysetValue<one.weight){
			emptysetValue = one.weight;
		}
		return two;
	}
}

lbool MaxAgg::canPropagateHead(){
	if ((lower && set->currentbestcertain > bound) || (!lower && set->currentbestpossible < bound)) {
		return l_False;
	} else if ((lower && set->currentbestpossible <= bound) || (!lower && set->currentbestcertain >= bound)) {
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
	Clause* confl = NULL;
	if (headtrue && lower) {
		vector<int>::size_type i=0;
		while( confl == NULL && i<set->wlitset.size() && bound<set->wlitset[i].weight){
			confl = AggSolver::aggsolver->notifySATsolverOfPropagation(~set->wlitset[i].lit, new AggrReason(this, NEG, i));
			i++;
		}
	}else if(!headtrue && !lower){
		vector<int>::size_type i=0;
		while( confl == NULL && i<set->wlitset.size() && bound<=set->wlitset[i].weight){
			confl = AggSolver::aggsolver->notifySATsolverOfPropagation(~set->wlitset[i].lit, new AggrReason(this, NEG, i));
			i++;
		}
	}
	return confl;
}

/**
 * If only one value is still possible and the head has already been derived, then this last literal
 * might also be propagated
 *
 * head is true  && A <= AGG: Last literal has to be true
 * head is true  && AGG <= B: No conclusion possible (emptyset is also a solution)
 * head is false && A <= AGG: No conclusion possible (emptyset is also a solution)
 * head is false && AGG <= B: Last literal has to be true
 */
Clause* MaxAgg::propagate(bool headtrue) {
	Clause* confl = NULL;
	if(set->possiblecount==1 && ((headtrue && !lower) || (!headtrue && lower))){
		for(vector<WLit>::size_type i=0; i<set->wlitset.size(); i++){
			if(set->litvalue[i]==l_Undef){
				confl = AggSolver::aggsolver->notifySATsolverOfPropagation(set->wlitset[i].lit, new AggrReason(this, POS, i));
				break;
			}
		}
	}
	return confl;
}

/*****************
 * SUM AGGREGATE *
 *****************/

int AggrSumSet::getBestPossible() {
	int max = emptysetValue;
	for (vector<Lit>::size_type j = 0; j < wlitset.size(); j++) {
		max += wlitset[j].weight;
	}
	return max;
}

void AggrSumSet::removeFromCertainSet(WLit l){
	truecount--;
	if (truecount == 0) {
		currentbestcertain = emptysetValue;
	}else{
		currentbestcertain -= l.weight;
	}
}

void AggrSumSet::addToCertainSet(WLit l){
	truecount++;
	currentbestcertain += l.weight;
}

void AggrSumSet::addToPossibleSet(WLit l){
	possiblecount++;
	currentbestpossible += l.weight;
}

void AggrSumSet::removeFromPossibleSet(WLit l){
	possiblecount--;
	if(possiblecount==0){
		currentbestpossible = emptysetValue;
	}else{
		currentbestpossible -= l.weight;
	}
}

/**
 * multi-set semantics!
 */
int	AggrSumSet::getCombinedWeight(int first, int second){
	return first+second;
}

WLit AggrSumSet::handleOccurenceOfBothSigns(WLit one, WLit two){
	if(one.weight<two.weight){
		emptysetValue += one.weight;
		return WLit(two.lit, two.weight-one.weight);
	}else{
		emptysetValue += two.weight;
		return WLit(one.lit, one.weight-two.weight);
	}
}

/*********************
 * PRODUCT AGGREGATE *
 *********************/

int AggrProdSet::getBestPossible() {
	int max = emptysetValue;
	for (vector<Lit>::size_type j = 0; j < wlitset.size(); j++) {
		max *= wlitset[j].weight;
	}
	return max;
}

void AggrProdSet::removeFromCertainSet(WLit l){
	truecount--;
	if (truecount == 0) {
		currentbestcertain = emptysetValue;
	}else{
		currentbestcertain /= l.weight;
	}
}

void AggrProdSet::addToCertainSet(WLit l){
	truecount++;
	currentbestcertain *= l.weight;
}

void AggrProdSet::addToPossibleSet(WLit l){
	possiblecount++;
	currentbestpossible *= l.weight;
}

void AggrProdSet::removeFromPossibleSet(WLit l){
	possiblecount--;
	if(possiblecount==0){
		currentbestpossible = emptysetValue;
	}else{
		currentbestpossible /= l.weight;
	}
}

/**
 * multi-set semantics!
 */
int	AggrProdSet::getCombinedWeight(int first, int second){
	return first*second;
}

WLit AggrProdSet::handleOccurenceOfBothSigns(WLit one, WLit two){
	//NOTE: om dit toe te laten, ofwel bij elke operatie op en literal al zijn voorkomens overlopen
	//ofwel aggregaten voor doubles ondersteunen (het eerste is eigenlijk de beste oplossing)
	//Mogelijke eenvoudige implementatie: weigts bijhouden als doubles (en al de rest als ints)
	reportf("Product aggregates in which both the literal and its negation occur "
			"are currently not supported. Replace %s%d or %s%d by a tseitin.\n",
			sign(one.lit)?"-":"", var(one.lit)+1, sign(two.lit)?"-":"", var(two.lit)+1); exit(3);
}

lbool SPAgg::canPropagateHead(){
	if ((lower && set->currentbestcertain > bound) || (!lower && set->currentbestpossible < bound)) {
		return l_False;
	} else if ((lower && set->currentbestpossible <= bound) || (!lower && set->currentbestcertain >= bound)) {
		return l_True;
	} else {
		return l_Undef;
	}
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
	vector<WLit>::iterator pos;
	int weightbound;

	//determine the lower bound of which weight literals to consider
	if (headtrue) {
		if(lower){
			if(sum){
				weightbound = bound-set->currentbestcertain;
			}else{
				//currentbestcertain = 0 not possible (always geq 1)
				weightbound = bound/set->currentbestcertain;
			}
			//+1 because larger and not eq
			weightbound++;
		}else{
			if(sum){
				weightbound = set->currentbestpossible-bound;
			}else{
				//if bound == 0, it is never possible to obtain a smaller product, so get first weight larger than 0
				weightbound = bound==0?0:set->currentbestpossible/bound;
			}
			//+1 because larger and not eq
			weightbound++;
		}
	} else {
		if(lower){
			if(sum){
				weightbound = set->currentbestpossible-bound;
			}else{
				//if bound == 0, it is never possible to obtain a smaller product, so get first weight larger than 0
				weightbound = bound==0?0:set->currentbestpossible/bound;
			}
		}else{
			if(sum){
				weightbound = bound - set->currentbestcertain;
			}else{
				//currentbestcertain = 0 not possible (always leq 1)
				weightbound = bound/set->currentbestcertain;
			}
		}
	}
	pos = lower_bound(set->wlitset.begin(), set->wlitset.end(), weightbound);
	if(pos==set->wlitset.end()){
		return c;
	}

	//find the index of the literal
	int start = 0;
	vector<WLit>::iterator it = set->wlitset.begin();
	while(it!=pos){
		it++; start++;
	}
	for (vector<Lit>::size_type u = start; c==NULL && u < set->wlitset.size(); u++) {
		if (set->litvalue[u]==l_Undef) {// no conflicts possible (because setting an unknown literal
			if((lower && headtrue) || (!lower && !headtrue)){
				c = AggSolver::aggsolver->notifySATsolverOfPropagation(~set->wlitset[u].lit, new AggrReason(this, NEG, u));
			}else{
				c = AggSolver::aggsolver->notifySATsolverOfPropagation(set->wlitset[u].lit, new AggrReason(this, POS, u));
			}
		}
	}
	return c;
}

/*******************
 * CLAUSE LEARNING *
 *******************/

/**
 * ALL SIGNS INVERTED TO MAKE A CLAUSE
 *
 * empty set: +INFINITY
 *
 * head true & AGG <= B: one literal that is true and smaller/eq than B
 * 			   A <= AGG: all literals with weight smaller than A
 * head false & AGG <= B: all literals with weight smaller/eq than B
 * 				A <= AGG: one literal that is true and smaller than A
 * type is pos & AGG <= B: head is true and all other smaller/eq ones are false
 * 				 A <= AGG: head is false and all other smaller ones are false
 * type is neq & AGG <= B: head is false
 * 				 A <= AGG: head is true
 */
void MinAgg::getExplanation(Lit p, vec<Lit>& lits, AggrReason& ar){
	if (ar.type == HEAD) {
		if (ar.expr->head == p) {
			if(lower){
				for(int i=0; i<set->stack.size(); i++){
					if(set->stack[i].type==POS && set->stack[i].wlit.weight<=bound){
						lits.push(~set->stack[i].wlit.lit);
						break;
					}
				}
			}else{
				for(vector<Lit>::size_type i=0; i<set->wlitset.size() && set->wlitset[i].weight < bound; i++){
					lits.push(set->wlitset[i].lit);
				}
			}
		} else {
			if(lower){
				for(vector<Lit>::size_type i=0; i<set->wlitset.size() && set->wlitset[i].weight <= bound; i++){
					lits.push(set->wlitset[i].lit);
				}
			}else{
				for(int i=0; i<set->stack.size(); i++){
					if(set->stack[i].type==POS && set->stack[i].wlit.weight<bound){
						lits.push(~set->stack[i].wlit.lit);
						break;
					}
				}
			}
		}
	} else if (ar.type == POS) {
		if(lower){
			lits.push(~head);
			for(vector<Lit>::size_type i=0; i<set->wlitset.size() && set->wlitset[i].weight<=bound; i++){
				if(set->wlitset[i].lit!=p){
					lits.push(set->wlitset[i].lit);
				}
			}
		}else{
			lits.push(head);
			for(vector<Lit>::size_type i=0; i<set->wlitset.size() && set->wlitset[i].weight<bound; i++){
				if(set->wlitset[i].lit!=p){
					lits.push(set->wlitset[i].lit);
				}
			}
		}
	} else {//NEG type
		if(lower){
			lits.push(head);
		}else{
			lits.push(~head);
		}
	}
}

/**
 * ALL SIGNS INVERTED TO MAKE A CLAUSE
 *
 * empty set: -INFINITY
 *
 * head true & AGG <= B: all literals false with weight larger than B
 * 			   A <= AGG: one literal true and larger/eq than A
 * head false & AGG <= B: one literal true and larger than B
 * 				A <= AGG: all literals false with weight larger/eq than A
 * type is pos & AGG <= B: head is false and all other larger ones are false
 * 				 A <= AGG: head is true and all other larger/eq ones are false
 * type is neq & AGG <= B: head is true
 * 				 A <= AGG: head is false
 */
void MaxAgg::getExplanation(Lit p, vec<Lit>& lits, AggrReason& ar){
	if (ar.type == HEAD) {
		if (ar.expr->head == p) {
			if(lower){
				for(vector<Lit>::size_type i=0; i<set->wlitset.size(); i++){
					if(set->wlitset[i].weight > bound){
						lits.push(set->wlitset[i].lit);
					}
				}
			}else{
				for(int i=0; i<set->stack.size(); i++){
					if(set->stack[i].type==POS && set->stack[i].wlit.weight>=bound){
						lits.push(~set->stack[i].wlit.lit);
						break;
					}
				}
			}
		} else {
			if(lower){
				for(int i=0; i<set->stack.size(); i++){
					if(set->stack[i].type==POS && set->stack[i].wlit.weight>bound){
						lits.push(~set->stack[i].wlit.lit);
						break;
					}
				}
			}else{
				for(vector<Lit>::size_type i=0; i<set->wlitset.size(); i++){
					if(set->wlitset[i].weight >= bound){
						lits.push(set->wlitset[i].lit);
					}
				}
			}
		}
	} else if (ar.type == POS) {
		if(lower){
			lits.push(head);
			for(vector<Lit>::size_type i=0; i<set->wlitset.size(); i++){
				if(set->wlitset[i].weight>bound && set->wlitset[i].lit!=p){
					lits.push(set->wlitset[i].lit);
				}
			}
		}else{
			lits.push(~head);
			for(vector<Lit>::size_type i=0; i<set->wlitset.size(); i++){
				if(set->wlitset[i].weight>=bound && set->wlitset[i].lit!=p){
					lits.push(set->wlitset[i].lit);
				}
			}
		}
	} else {//NEG type
		if(lower){
			lits.push(~head);
		}else{
			lits.push(head);
		}
	}
}

/**
 * INVERTED SIGNS FOR CLAUSE!
 *
 * empty set is 0
 *
 * head true & AGG <= B: from the stack, keep adding false literals until possiblesum <= B
 * 			   A <= AGG: from the stack, keep adding true literals until A <= certainsum
 * head false & AGG <= B: from the stack, keep adding true literals until certainsum > B
 * 			    A <= AGG: from the stack, keep adding false literals until possiblesum < A
 * type is pos & AGG <= B: head is false and from the stack,
 * 					keep adding false literals until possiblesum - lit itself <= B
 * 			     A <= AGG: head is true and from the stack,
 * 					keep adding false literals until A > possiblesum - lit itself
 * type is neg & AGG <= B: head is true and from the stack,
 * 					keep adding true literals until certainsum + lit itself > B
 * 			     A <= AGG: head is false and from the stack,
 * 					keep adding true literals until A <= certainsum + lit itself
 *
 * true meaning that the literal has the same sign as in the set
 * false meaning that the literal has the opposite sign as compared to the set
 */
void SPAgg::getExplanation(Lit p, vec<Lit>& lits, AggrReason& ar){
	int possiblesum, certainsum;
	certainsum = set->emptysetValue;
	possiblesum = set->getBestPossible();

	if(ar.type == POS){
		if(sum){
			possiblesum -= set->wlitset[ar.index].weight;
		}else{
			possiblesum /= set->wlitset[ar.index].weight;
		}

	}else if(ar.type == NEG){
		if(sum){
			certainsum += set->wlitset[ar.index].weight;
		}else{
			certainsum *= set->wlitset[ar.index].weight;
		}
	}

	bool explained = false, headfound = false, addhead = false;

	//an explanation can exist without any other set literals, so check for this
	if(ar.type==NEG && ((lower && certainsum > bound) || (!lower && certainsum >= bound))){
		explained = true;
	}
	if(ar.type==POS && ((lower && possiblesum <= bound) || (!lower && possiblesum < bound))){
		explained = true;
	}
	if(ar.type==HEAD){
		headfound = true;
	}

	if(headindex==0){
		headfound = true;
		addhead = true;
	}
	for(int i=0; !(headfound && explained) && i<set->stack.size() && set->stack[i].wlit.lit!=p; i++){
		if(headindex==i+1){
			headfound = true;
			addhead = true;
		}
		if(set->stack[i].type == POS){ //means that the literal in the set became true
			if(sum){
				certainsum += set->stack[i].wlit.weight;
			}else{
				certainsum *= set->stack[i].wlit.weight;
			}

			if(ar.type==HEAD){
				if(head==p && !lower){
					lits.push(~set->stack[i].wlit.lit);
					if(bound <= certainsum){
						explained = true;
					}
				}else if(head==~p && lower){
					lits.push(~set->stack[i].wlit.lit);
					if(bound < certainsum){
						explained = true;
					}
				}
			}else if(ar.type==NEG){
				if(!explained){ //for NEG, you have to keep searching until also the head has been added
					lits.push(~set->stack[i].wlit.lit);
					if((lower && certainsum > bound) || (!lower && certainsum >= bound)){
						explained = true;
					}
				}
			}
		}else if(set->stack[i].type == NEG){ //the literal in the set became false
			if(sum){
				possiblesum -= set->stack[i].wlit.weight;
			}else{
				possiblesum /= set->stack[i].wlit.weight;
			}

			if(ar.type==HEAD){
				if(head==p && lower){
					lits.push(~set->stack[i].wlit.lit);
					if(possiblesum <= bound){
						explained = true;
					}
				}else if(head==~p && !lower){
					lits.push(~set->stack[i].wlit.lit);
					if(possiblesum < bound){
						explained = true;
					}
				}
			}else if(ar.type==POS){
				if(!explained){ //for POS, you have to keep searching until also the head has been added
					lits.push(~set->stack[i].wlit.lit);
					if((lower && possiblesum <= bound) || (!lower && possiblesum < bound)){
						explained = true;
					}
				}
			}
		}
	}
	if(addhead){
		if((ar.type == POS && lower) || (ar.type == NEG && !lower)){
			lits.push(head);
		}else{
			lits.push(~head);
		}
	}

	assert(headfound && explained);
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

inline bool AggrSet::oppositeIsJustified(int index, vec<int>& currentjust, bool real){
	if(real){
		return litvalue[index]!=l_True;
	}else{
		return litvalue[index]!=l_True && (!sign(wlitset[index].lit) || isJustified(var(wlitset[index].lit), currentjust));
	}
}
inline bool AggrSet::isJustified(int index, vec<int>& currentjust, bool real){
	if(real){
		return litvalue[index]!=l_False;
	}else{
		return litvalue[index]!=l_False && (sign(wlitset[index].lit) || isJustified(var(wlitset[index].lit), currentjust));
	}
}
inline bool AggrSet::isJustified(Var x, vec<int>& currentjust){
	return currentjust[x]==0;
}

/**
 * Finds a new justification.
 * @pre: head is not false, so a justification exists
 */
void Agg::becomesCycleSource(vec<Lit>& j){
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
void MinAgg::createLoopFormula(const std::set<Var>& ufs, vec<Lit>& loopf, vec<int>& seen){
	vector<WLit> lits = set->wlitset;
	if(lower){
		for (vector<int>::size_type i=0; i<lits.size() && lits[i].weight <= bound; ++i) {
			Lit l = lits[i].lit;
			if (ufs.find(var(l)) == ufs.end() && seen[var(l)] != (sign(l) ? 1 : 2)) {
				loopf.push(l);
				seen[var(l)] = (sign(l) ? 1 : 2);
			}
		}
	}else{
		for (vector<int>::size_type i=0; i<lits.size() && lits[i].weight < bound; ++i) {
			Lit l = lits[i].lit;
			if (ufs.find(var(l)) == ufs.end() && seen[var(l)] != (sign(l) ? 2 : 1)) {
				loopf.push(~l);
				seen[var(l)] = (sign(l) ? 2 : 1);
			}
		}
	}
}

/**
 * AGG <= B: v is justified if one literal below/eq the bound is THAT IS NOT THE HEAD
 * 					if so, change the justification to the literal
 * 					otherwise, add all nonfalse, non-justified, relevant, below the bound literals to the queue
 * A <= AGG: v is justified if the negation of all literals below the bound are. The emptyset is always a solution,
 * 			 so no conclusions have to be drawn from the literals above/eq the bound
 * 					if so, change the justification to the negation of all those below the bound literals
 * 					otherwise, add all nonfalse, non-justified, relevant, below the bound literals to the queue
 * NOTE it might be possible to write this more efficiently, for some ideas see commits before 26/01/2010
 */
bool MinAgg::canJustifyHead(vec<Lit>& jstf, vec<Var>& nonjstf, vec<int>& currentjust, bool real){
	vector<WLit> lits = set->wlitset;
	bool justified = false;
	if(lower){
		for (vector<int>::size_type i=0; i<lits.size() && lits[i].weight<=bound; ++i) {
			Lit l = lits[i].lit;
			if(set->isJustified(i, currentjust, real)){
				jstf.push(l);
				justified = true;
			}else{
				nonjstf.push(var(l));
			}
		}
	}else{
		for (vector<int>::size_type i=0; i<lits.size() && lits[i].weight<bound; ++i) {
			Lit l = lits[i].lit;
			if(set->oppositeIsJustified(i, currentjust, real)){
				jstf.push(~l); //push negative literal, because it should become false
			}else{
				nonjstf.push(var(l));
			}
		}
		if (nonjstf.size()==0) {
			justified = true;
		}
	}
	if(!justified){
		jstf.clear();
	}
	return justified;
}

void MaxAgg::createLoopFormula(const std::set<Var>& ufs, vec<Lit>& loopf, vec<int>& seen){
	vector<WLit> lits = set->wlitset;
	if(lower){
		bool end = false;
		for (vector<int>::size_type i=lits.size()-1; !end && lits[i].weight>bound; i--) {
			if(i==0){ end = true; }
			Lit l = lits[i].lit;
			if (l!=head && ufs.find(var(l)) == ufs.end() && seen[var(l)] != (sign(l) ? 2 : 1)) {
				loopf.push(~l);
				seen[var(l)] = (sign(l) ? 2 : 1);
			}
		}
	}else{
		bool end = false;
		for (vector<int>::size_type i=lits.size()-1; !end && lits[i].weight>=bound; i--) {
			if(i==0){ end = true; }
			Lit l = lits[i].lit;
			if (l!=head &&  ufs.find(var(l)) == ufs.end() && seen[var(l)] != (sign(l) ? 1 : 2)) {
				loopf.push(l);
				seen[var(l)] = (sign(l) ? 1 : 2);
			}
		}
	}
}

bool MaxAgg::canJustifyHead(vec<Lit>& jstf, vec<Var>& nonjstf, vec<int>& currentjust, bool real){
	vector<WLit> lits = set->wlitset;
	bool justified = false;
	if(lower){
		bool end = false;
		for (vector<int>::size_type i=lits.size()-1; !end && lits[i].weight>bound; i--) {
			if(i==0){ end = true; }
			Lit l = lits[i].lit;
			if(set->oppositeIsJustified(i, currentjust, real)){
				jstf.push(~l); //push negative literal, because it should become false
				nonjstf.push(var(l));
			}
		}
		if(nonjstf.size()==0){
			justified = true;
		}
	}else{
		bool end = false;
		for (vector<int>::size_type i=lits.size()-1; !end && lits[i].weight>=bound; i--) {
			if(i==0){ end = true; }
			Lit l = lits[i].lit;
			if(set->isJustified(i, currentjust, real)){
				jstf.push(l);
				justified = true;
			}else{
				nonjstf.push(var(l));
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
void SPAgg::createLoopFormula(const std::set<Var>& ufs, vec<Lit>& loopf, vec<int>& seen){
	if(lower){
		for (vector<int>::size_type i = 0; i < set->wlitset.size(); ++i) {
			Lit l = set->wlitset[i].lit;
			if (l!=head && ufs.find(var(l)) == ufs.end() && seen[var(l)] != (sign(l) ? 1 : 2)) {
				loopf.push(~l);
				seen[var(l)] = (sign(l) ? 1 : 2);
			}
		}
	}else{
		for (vector<int>::size_type i = 0; i < set->wlitset.size(); ++i) {
			Lit l = set->wlitset[i].lit;
			if (l!=head && ufs.find(var(l)) == ufs.end() && seen[var(l)] != (sign(l) ? 2 : 1)) {
				loopf.push(l);
				seen[var(l)] = (sign(l) ? 2 : 1);
			}
		}
	}
}

/**
 * AGG <= B: add a number of justified literals such that they guarantee the bestpossible value is below the bound
 * A <= AGG: need a justification of which the sum exceed/eq the bound
 */
bool SPAgg::canJustifyHead(vec<Lit>& jstf, vec<Var>& nonjstf, vec<int>& currentjust, bool real){
	vector<WLit> lits = set->wlitset;
	bool justified = false;
	if(lower){
		int bestpossible = set->getBestPossible();
		for (vector<int>::size_type i = 0; !justified && i < lits.size(); ++i) {
			Lit l = lits[i].lit;
			if(set->oppositeIsJustified(i, currentjust, real)){
				jstf.push(~l);
				if(sum){
					bestpossible -= lits[i].weight;
				}else{
					bestpossible /= lits[i].weight;
				}
				if (bestpossible <= bound){
					justified = true;
				}
			}else{
				nonjstf.push(var(l));
			}
		}
	}else{
		int bestcertain = set->emptysetValue;
		for (vector<int>::size_type i = 0; !justified && i < lits.size(); ++i) {
			Lit l = lits[i].lit;
			if(set->isJustified(i, currentjust, real)){
				jstf.push(l);
				if(sum){
					bestcertain += lits[i].weight;
				}else{
					bestcertain *= lits[i].weight;
				}
				if (bestcertain >= bound){
					justified = true;
				}
			}else{
				nonjstf.push(var(l));
			}
		}
	}
	return justified;
}
