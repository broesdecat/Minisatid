#include "Agg.h"
#include "AggSolver.h"
#include <algorithm>

void Agg::backtrack(Occurrence tp, int index) {
	PropagationInfo pi = stack.last();
	stack.pop();

	if (tp == HEAD){ //propagation didn't affect min/max
		headvalue = l_Undef;
		return;
	}

	litvalue[index] = l_Undef;
	if (pi.type == POS) {
		removeFromCertainSet(pi.wlit);
	}else{
		addToPossibleSet(pi.wlit);
	}
}

Clause* Agg::propagate(Lit p, AggrWatch& ws){
	Clause* confl = NULL;

	//FIXME: error if p is head
	Occurrence tp = relativeOccurrence(ws.type, p);
	stack.push(PropagationInfo(p, set->wlitset[ws.index].weight,tp));

	if (tp == HEAD){ // The head literal has been propagated
		assert(headvalue==l_Undef);
		headvalue = sign(p)?l_False:l_True;
		confl = propagateHead(headvalue==l_True);
	}else { // It's a set literal.
		litvalue[ws.index] = tp==POS?l_True:l_False;
		tp==POS? addToCertainSet(set->wlitset[ws.index]):removeFromPossibleSet(set->wlitset[ws.index]);

		lbool result = canPropagateHead();
		if(result==l_True){
			confl = AggSolver::aggsolver->notifySATsolverOfPropagation(head, new AggrReason(this, HEAD, -1));
		}else if(result==l_False){
			confl = AggSolver::aggsolver->notifySATsolverOfPropagation(~head, new AggrReason(this, HEAD, -1));
		}else if(headvalue != l_Undef){ //the head cannot be directly propagated, but its value has already been found
			confl = propagate(headvalue==l_True);
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
void Agg::doSetReduction() {
	vector<WLit> oldset = set->wlitset;

	//Sort all wlits according to the integer representation of their literal (to get all literals next to each other)
	std::sort(oldset.begin(), oldset.end(), compareLits);

	AggrSet* newset = new AggrSet();
	int indexinnew = 0;
	newset->wlitset.push_back(oldset[indexinnew]);

	bool setisreduced = false;
	for(vector<int>::size_type i=1; i<oldset.size(); i++){
		WLit oldl = newset->wlitset[indexinnew];
		WLit newl = oldset[i];
		if(var(oldl.lit)==var(newl.lit)){ //same variable
			setisreduced = true;
			if(oldl.lit==newl.lit){ //same literal, keep combined weight
				newset->wlitset[indexinnew].weight = getCombinedWeight(newl.weight, oldl.weight);
			}else{ //opposite signs
				newset->wlitset[indexinnew] = handleOccurenceOfBothSigns(oldl, newl);
			}
		}else{
			newset->wlitset.push_back(newl);
			indexinnew++;
		}
	}

	//important to sort again to guarantee that it is sorted according to the weights
	std::sort(newset->wlitset.begin(), newset->wlitset.end());

	if(setisreduced){
		AggSolver::aggsolver->aggr_sets.push(newset);
		set = newset;
	}else{
		delete newset;
	}
}

void Agg::initialize(){
	currentbestpossible = getBestPossible();
	currentbestcertain = emptysetValue;
	possiblecount = set->wlitset.size();
}

/*****************
 * MIN AGGREGATE *
 *****************/

MinAgg::~MinAgg() {
}

int MinAgg::getBestPossible() {
	int min = emptysetValue;
	for (vector<Lit>::size_type j = 0; j < set->wlitset.size(); j++) {
		if(min > set->wlitset[j].weight){
			min = set->wlitset[j].weight;
		}
	}
	return min;
}

void MinAgg::removeFromCertainSet(WLit l){
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

void MinAgg::addToCertainSet(WLit l){
	truecount++;
	if(l.weight<currentbestcertain){
		currentbestcertain = l.weight;
	}
}

void MinAgg::addToPossibleSet(WLit l){
	possiblecount++;
	if(l.weight<currentbestpossible){
		currentbestpossible = l.weight;
	}
}

void MinAgg::removeFromPossibleSet(WLit l){
	possiblecount--;
	if(possiblecount==0){
		currentbestpossible = emptysetValue;
	}else{
		if(l.weight==currentbestpossible){
			currentbestpossible = emptysetValue;
			for(vector<Lit>::size_type i=0; i<set->wlitset.size(); i++){
				if(litvalue[i] != l_False && set->wlitset[i].weight<currentbestpossible){
					currentbestpossible = set->wlitset[i].weight;
				}
			}
		}
	}
}

lbool MinAgg::canPropagateHead() {
	if ((lower && currentbestpossible > bound) || (!lower && currentbestcertain < bound)) {
		return l_False;
	} else if ((lower && currentbestcertain <= bound) || (!lower && currentbestpossible >= bound)) {
		return l_True;
	} else {
		return l_Undef;
	}
}

int	MinAgg::getCombinedWeight(int first, int second){
	return first<second?first:second;
}

WLit MinAgg::handleOccurenceOfBothSigns(WLit one, WLit two){
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

/**
 * head is true  && A <= AGG:
 * 		make all literals false with weight smaller than bound
 * head is false && AGG <= B:
 * 		make all literals false with weight smaller/eq than bound
 */
Clause* MinAgg::propagateHead(bool headtrue) {
	Clause* confl = NULL;
	if (headtrue && !lower) {
		int i=0;
		while( confl == NULL && set->wlitset[i].weight<bound){
			confl = AggSolver::aggsolver->notifySATsolverOfPropagation(~set->wlitset[i].lit, new AggrReason(this, NEG, i));
			i++;
		}
	}else if(!headtrue && lower){
		int i=0;
		while( confl == NULL && set->wlitset[i].weight<=bound){
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
	if(possiblecount==1 && ((headtrue && lower) || (!headtrue && !lower))){
		for(vector<WLit>::size_type i=0; i<set->wlitset.size(); i++){
			if(litvalue[i]==l_Undef){
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

MaxAgg::~MaxAgg() {
}

int MaxAgg::getBestPossible() {
	int max = emptysetValue;

	for (vector<Lit>::size_type j = 0; j < set->wlitset.size(); j++) {
		if(max < set->wlitset[j].weight){
			max = set->wlitset[j].weight;
		}
	}
	return max;
}

void MaxAgg::removeFromCertainSet(WLit l){
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

void MaxAgg::addToCertainSet(WLit l){
	truecount++;
	if(l.weight>currentbestcertain){
		currentbestcertain = l.weight;
	}
}

void MaxAgg::addToPossibleSet(WLit l){
	possiblecount++;
	if(l.weight>currentbestpossible){
		currentbestpossible = l.weight;
	}
}

void MaxAgg::removeFromPossibleSet(WLit l){
	possiblecount--;
	if(possiblecount==0){
		currentbestpossible = emptysetValue;
	}else{
		if(l.weight==currentbestpossible){
			currentbestpossible = emptysetValue;
			for(vector<Lit>::size_type i=0; i<set->wlitset.size(); i++){
				if(litvalue[i] != l_False && currentbestpossible < set->wlitset[i].weight){
					currentbestpossible = set->wlitset[i].weight;
				}
			}
		}
	}
}

lbool MaxAgg::canPropagateHead(){
	if ((lower && currentbestcertain > bound) || (!lower && currentbestpossible < bound)) {
		return l_False;
	} else if ((lower && currentbestpossible <= bound) || (!lower && currentbestcertain >= bound)) {
		return l_True;
	} else {
		return l_Undef;
	}
}

int	MaxAgg::getCombinedWeight(int first, int second){
	return first>second?first:second;
}

WLit MaxAgg::handleOccurenceOfBothSigns(WLit one, WLit two){
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

/**
 * head is true  && AGG <= B:
 * 		make all literals false with weight larger than bound
 * head is false && A <= AGG:
 * 		make all literals false with weight larger/eq than bound
 */
Clause* MaxAgg::propagateHead(bool headtrue) {
	Clause* confl = NULL;
		if (headtrue && lower) {
			int i=0;
			while( confl == NULL && bound<set->wlitset[i].weight){
				confl = AggSolver::aggsolver->notifySATsolverOfPropagation(~set->wlitset[i].lit, new AggrReason(this, NEG, i));
				i++;
			}
		}else if(!headtrue && !lower){
			int i=0;
			while( confl == NULL && bound<=set->wlitset[i].weight){
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
	if(possiblecount==1 && ((headtrue && !lower) || (!headtrue && lower))){
		for(vector<WLit>::size_type i=0; i<set->wlitset.size(); i++){
			if(litvalue[i]==l_Undef){
				confl = AggSolver::aggsolver->notifySATsolverOfPropagation(set->wlitset[i].lit, new AggrReason(this, POS, i));
				break;
			}
		}
	}
	return confl;
}

/*********************
 * SUM-PRODUCT AGGREGATE *
 *********************/

SPAgg::~SPAgg() {
}

int SPAgg::getBestPossible() {
	int max = emptysetValue;
	for (vector<Lit>::size_type j = 0; j < set->wlitset.size(); j++) {
		if(sum){
			max += set->wlitset[j].weight;
		}else{
			max *= set->wlitset[j].weight;
		}
	}
	return max;
}

void SPAgg::removeFromCertainSet(WLit l){
	truecount--;
	if (truecount == 0) {
		currentbestcertain = emptysetValue;
	}else{
		if(sum){
			currentbestcertain -= l.weight;
		}else{
			currentbestcertain /= l.weight;
		}
	}
}

void SPAgg::addToCertainSet(WLit l){
	truecount++;
	if(sum){
		currentbestcertain += l.weight;
	}else{
		currentbestcertain *= l.weight;
	}
}

void SPAgg::addToPossibleSet(WLit l){
	possiblecount++;
	if(sum){
		currentbestpossible += l.weight;
	}else{
		currentbestpossible *= l.weight;
	}
}

void SPAgg::removeFromPossibleSet(WLit l){
	possiblecount--;
	if(possiblecount==0){
		currentbestpossible = emptysetValue;
	}else{
		if(sum){
			currentbestpossible -= l.weight;
		}else{
			currentbestpossible /= l.weight;
		}
	}
}

lbool SPAgg::canPropagateHead(){
	if ((lower && currentbestcertain > bound) || (!lower && currentbestpossible < bound)) {
		return l_False;
	} else if ((lower && currentbestpossible <= bound) || (!lower && currentbestcertain >= bound)) {
		return l_True;
	} else {
		return l_Undef;
	}
}

/**
 * multi-set semantics!
 */
int	SPAgg::getCombinedWeight(int first, int second){
	if(sum){
		return first+second;
	}else{
		return first*second;
	}
}

WLit SPAgg::handleOccurenceOfBothSigns(WLit one, WLit two){
	if(!sum){
		//TODO: om dit toe te laten, ofwel bij elke operatie op en literal al zijn voorkomens overlopen
		//ofwel aggregaten voor doubles ondersteunen (het eerste is eigenlijk de beste oplossing)
		//Mogelijke eenvoudige implementatie: weigts bijhouden als doubles (en al de rest als ints)
		reportf("Product aggregates in which both the literal and its negation occur "
				"are currently not supported. Replace %s%d or %s%d by a tseitin.\n",
				sign(one.lit)?"-":"", var(one.lit)+1, sign(two.lit)?"-":"", var(two.lit)+1); exit(3);
	}
	if(one.weight<two.weight){
		emptysetValue += one.weight;
		return WLit(two.lit, two.weight-one.weight);
	}else{
		emptysetValue += two.weight;
		return WLit(one.lit, one.weight-two.weight);
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
				weightbound = bound-currentbestcertain;
			}else{
				//currentbestcertain = 0 not possible (always geq 1)
				weightbound = bound/currentbestcertain;
			}
			//+1 because larger and not eq
			weightbound++;
		}else{
			if(sum){
				weightbound = currentbestpossible-bound;
			}else{
				//if bound == 0, it is never possible to obtain a smaller product, so get first weight larger than 0
				weightbound = bound==0?0:currentbestpossible/bound;
			}
			//+1 because larger and not eq
			weightbound++;
		}
	} else {
		if(lower){
			if(sum){
				weightbound = currentbestpossible-bound;
			}else{
				//if bound == 0, it is never possible to obtain a smaller product, so get first weight larger than 0
				weightbound = bound==0?0:currentbestpossible/bound;
			}
		}else{
			if(sum){
				weightbound = bound - currentbestcertain;
			}else{
				//currentbestcertain = 0 not possible (always leq 1)
				weightbound = bound/currentbestcertain;
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
		if (litvalue[u]==l_Undef) {// no conflicts possible (because setting an unknown literal
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
				for(int i=0; i<stack.size(); i++){
					if(stack[i].type==POS && stack[i].wlit.weight<=bound){
						lits.push(~stack[i].wlit.lit);
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
				for(int i=0; i<stack.size(); i++){
					if(stack[i].type==POS && stack[i].wlit.weight<bound){
						lits.push(~stack[i].wlit.lit);
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
				for(int i=0; i<stack.size(); i++){
					if(stack[i].type==POS && stack[i].wlit.weight>=bound){
						lits.push(~stack[i].wlit.lit);
						break;
					}
				}
			}
		} else {
			if(lower){
				for(int i=0; i<stack.size(); i++){
					if(stack[i].type==POS && stack[i].wlit.weight>bound){
						lits.push(~stack[i].wlit.lit);
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
	certainsum = emptysetValue;
	possiblesum = getBestPossible();

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

	bool derived = false, explained = false, headfound = false;

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

	for(int i=0; !(headfound && explained) && i<stack.size() && stack[i].wlit.lit!=p; i++){
		if(stack[i].type == POS){ //means that the literal in the set became true
			if(sum){
				certainsum += stack[i].wlit.weight;
			}else{
				certainsum *= stack[i].wlit.weight;
			}

			if(ar.type==HEAD){
				if(head==p && !lower){
					lits.push(~stack[i].wlit.lit);
					if(bound <= certainsum){
						explained = true;
					}
				}else if(head==~p && lower){
					lits.push(~stack[i].wlit.lit);
					if(bound < certainsum){
						explained = true;
					}
				}
			}else if(ar.type==NEG){
				if(!explained){ //for NEG, you have to keep searching until also the head has been added
					lits.push(~stack[i].wlit.lit);
					if((lower && certainsum > bound) || (!lower && certainsum >= bound)){
						explained = true;
					}
				}
			}
		}else if(stack[i].type == NEG){ //the literal in the set became false
			if(sum){
				possiblesum -= stack[i].wlit.weight;
			}else{
				possiblesum /= stack[i].wlit.weight;
			}

			if(ar.type==HEAD){
				if(head==p && lower){
					lits.push(~stack[i].wlit.lit);
					if(possiblesum <= bound){
						explained = true;
					}
				}else if(head==~p && !lower){
					lits.push(~stack[i].wlit.lit);
					if(possiblesum < bound){
						explained = true;
					}
				}
			}else if(ar.type==POS){
				if(!explained){ //for POS, you have to keep searching until also the head has been added
					lits.push(~stack[i].wlit.lit);
					if((lower && possiblesum <= bound) || (!lower && possiblesum < bound)){
						explained = true;
					}
				}
			}
		}else{
			//head derived, can only happen once
			assert(!derived);
			derived = true;

			if((ar.type == POS && lower) || (ar.type == NEG && !lower)){
				lits.push(head);
			}else{
				lits.push(~head);
			}
			headfound = true;
		}
	}
	assert(headfound && explained);
}

/*************************
 * IDSOLVER PROPAGATIONS *
 *************************/

/**
 * Goes through all that are already justifified. If those together are enough to justify the head (making it TRUE!),
 * then return those as a justification
 *
 * use emtpysetvalue! (which might already be better than the default)
 *
 * AGG <= B: bestpossible > bound => NOT justifiable
 * 			 bestcertain <= bound => take the stack as justification (can be done better)
 * 			 else try to find one literal that is already justified and would make the head true
 * 					if not found, then not justifiable
 * A <= AGG: bestcertain < bound => NOT justifiable
 * 			 bestpossible >= bound => take stack as justification
 * 			 else check that all literals with a weight < bound are already justified. If this is the case
 * 				they all form the justification. Otherwise not justifiable.
 */
void MinAgg::propagateJustifications(vec<Lit>& jstf, vec<int>& nb_body_lits_to_justify){
	if(lower){ //AGG <= B
		if(currentbestpossible>bound){ // not justifiable
		}else if(currentbestcertain <= bound){
			for(int i=0; i<stack.size(); i++){
				if(stack[i].type!=HEAD){
					jstf.push(stack[i].wlit.lit);
				}
			}
			nb_body_lits_to_justify[var(head)] = 0;
		}else{
			for(vector<int>::size_type i=0; i<set->wlitset.size(); i++){
				if(nb_body_lits_to_justify[var(set->wlitset[i].lit)] == 0 && set->wlitset[i].weight<=bound){
					jstf.push(set->wlitset[i].lit);
					nb_body_lits_to_justify[var(head)] = 0;
					break;
				}
			}
		}
	}else{ //A <= AGG
		if(currentbestcertain<bound){ // not justifiable
		}else if(currentbestpossible >= bound){
			for(int i=0; i<stack.size(); i++){
				if(stack[i].type!=HEAD){
					jstf.push(stack[i].wlit.lit);
				}
			}
			nb_body_lits_to_justify[var(head)] = 0;
		}else{
			bool foundonenotjustified = false;
			for(vector<int>::size_type i=0; i<set->wlitset.size(); i++){
				if(set->wlitset[i].weight<bound){
					if(nb_body_lits_to_justify[var(set->wlitset[i].lit)] == 0){
						jstf.push(set->wlitset[i].lit);
					}else{
						foundonenotjustified = true;
						break;
					}
				}
			}
			if(foundonenotjustified){
				jstf.clear();
			}else{
				nb_body_lits_to_justify[var(head)] = 0;
			}
		}
	}
}

void MaxAgg::propagateJustifications(vec<Lit>& jstf, vec<int>& nb_body_lits_to_justify){
	if(lower){ //AGG <= B
		if(currentbestcertain>bound){ // not justifiable
		}else if(currentbestpossible <= bound){
			for(int i=0; i<stack.size(); i++){
				if(stack[i].type!=HEAD){
					jstf.push(stack[i].wlit.lit);
				}
			}
			nb_body_lits_to_justify[var(head)] = 0;
		}else{
			bool foundonenotjustified = false;
			for(vector<int>::size_type i=0; i<set->wlitset.size(); i++){
				if(set->wlitset[i].weight>bound){
					if(nb_body_lits_to_justify[var(set->wlitset[i].lit)] == 0){
						jstf.push(set->wlitset[i].lit);
					}else{
						foundonenotjustified = true;
						break;
					}
				}
			}
			if(foundonenotjustified){
				jstf.clear();
			}else{
				nb_body_lits_to_justify[var(head)] = 0;
			}
		}
	}else{ //A <= AGG
		if(currentbestpossible<bound){ // not justifiable
		}else if(currentbestcertain >= bound){
			for(int i=0; i<stack.size(); i++){
				if(stack[i].type!=HEAD){
					jstf.push(stack[i].wlit.lit);
				}
			}
			nb_body_lits_to_justify[var(head)] = 0;
		}else{
			for(vector<int>::size_type i=0; i<set->wlitset.size(); i++){
				if(nb_body_lits_to_justify[var(set->wlitset[i].lit)] == 0 && set->wlitset[i].weight>=bound){
					jstf.push(set->wlitset[i].lit);
					nb_body_lits_to_justify[var(head)] = 0;
					break;
				}
			}
		}
	}
}

/**
 * use emtpysetvalue! (which might already be better than the default)
 *
 * AGG <= B: bestcertain > bound => NOT justifiable
 * 			 bestpossible <= bound => take the stack as justification (can be done better)
 * 			 else take all false and unknown justified literals, until the bestpossible is below/eq B
 * A <= AGG: bestpossible < bound => NOT justifiable
 * 			 bestcertain >= bound => take stack as justification
 * 			 else take a sum of all non-false literals that are already justified and add them to the justification
 * 				until the sum is larger-eq than A
 */
void SPAgg::propagateJustifications(vec<Lit>& jstf, vec<int>& nb_body_lits_to_justify){
	if(lower){ //AGG <= B
		if(currentbestcertain>bound){ // not justifiable
		}else if(currentbestpossible <= bound){
			for(int i=0; i<stack.size(); i++){
				if(stack[i].type!=HEAD){
					jstf.push(stack[i].wlit.lit);
				}
			}
			nb_body_lits_to_justify[var(head)] = 0;
		}else{
			int bestposs = currentbestpossible;
			for(vector<int>::size_type i=0; bestposs>bound && i<set->wlitset.size(); i++){
				if(nb_body_lits_to_justify[var(set->wlitset[i].lit)] == 0){
					if(litvalue[i]==l_Undef){
						if(sum){
							bestposs -= set->wlitset[i].weight;
						}else{
							bestposs /= set->wlitset[i].weight;
						}
					}
					jstf.push(set->wlitset[i].lit);
				}
			}
			if(bestposs>bound){
				jstf.clear();
			}else{
				//TODO push here the stack also, because that can be part of the justification
				nb_body_lits_to_justify[var(head)] = 0;
			}
		}
	}else{ //A <= AGG
		if(currentbestpossible<bound){ // not justifiable
		}else if(currentbestcertain >= bound){
			for(int i=0; i<stack.size(); i++){
				if(stack[i].type!=HEAD){
					jstf.push(stack[i].wlit.lit);
				}
			}
			nb_body_lits_to_justify[var(head)] = 0;
		}else{
			int sum = emptysetValue;
			for(vector<int>::size_type i=0; i<set->wlitset.size(); i++){
				if(nb_body_lits_to_justify[var(set->wlitset[i].lit)] == 0 && litvalue[i] != l_False){
					jstf.push(set->wlitset[i].lit);
					if(this->sum){
						sum += set->wlitset[i].weight;
					}else{
						sum *= set->wlitset[i].weight;
					}

				}
			}
			if(sum>=bound){
				nb_body_lits_to_justify[var(head)] = 0;
			}else{
				jstf.clear();
			}
		}
	}
}

/**
 * Creates a new SP justification. According to an overestimating heuristic, it is decided whether the new justification
 * might not be cycle free, in which case it is added as a cycle source.
 *
 * @pre: v is not false, so a justification exists
 */
bool Agg::becomesCycleSource(vec<Lit>& nj){
	justifyHead(nj);
	assert(nj.size()>0);
	//TODO maybe some sign checking of the literals in the justification is also possible here (see old code), but it is not clear why
	return true;
}

/**
 * Justification for the head of the aggregate expression
 * @pre: head is not false
 *
 * AGG <= B: bestcertain <= bound => take the first element on the stack with a weight smaller/eq as bound (and POS!)
 * 			 else find a literal that is not false and with weight smaller/eq as b
 * A <= AGG: a justification will consist of the negation of all literals with value lower than A
 * 				no positive value is needed, because the empty set is also a solution
 */
void MinAgg::justifyHead(vec<Lit>& just){
	if(lower){
		if(currentbestcertain <= bound){
			for(int i=0; i<stack.size(); i++){
				if(stack[i].type==POS && stack[i].wlit.weight<=bound){
					just.push(stack[i].wlit.lit);
					break;
				}
			}
		}else{
			for(vector<int>::size_type i=0; i<set->wlitset.size(); i++){
				if(litvalue[i]!=l_False && set->wlitset[i].weight<=bound){
					just.push(set->wlitset[i].lit);
					break;
				}
			}
		}
	}else{
		for(vector<int>::size_type i=0; i<set->wlitset.size(); i++){
			if(set->wlitset[i].weight<bound){
				just.push(~set->wlitset[i].lit);
			}
		}
	}
}

/**
 * AGG <= B: add the negation of all literals with weight larger than B
 */
void MaxAgg::justifyHead(vec<Lit>& just){
	if(lower){
		for(vector<int>::size_type i=0; i<set->wlitset.size(); i++){
			if(set->wlitset[i].weight>bound){
				just.push(~set->wlitset[i].lit);
			}
		}
	}else{
		if(currentbestcertain >= bound){
			for(int i=0; i<stack.size(); i++){
				if(stack[i].type==POS && stack[i].wlit.weight<=bound){
					just.push(stack[i].wlit.lit);
					break;
				}
			}
		}else{
			for(vector<int>::size_type i=0; i<set->wlitset.size(); i++){
				if(litvalue[i]!=l_False && set->wlitset[i].weight>=bound){
					just.push(set->wlitset[i].lit);
					break;
				}
			}
		}
	}
}

/**
 * AGG <= B: add the negation of a number of non-true literals in the set until the bestpossible value is below/eq B
 * A <= AGG: bestpossible < bound => NOT justifiable
 * 			 bestcertain >= bound => take the first element on the stack with a weight smaller/eq as bound (and POS!)
 * 			 else take a number of true/unknown literals until the sum is large enough
 */
void SPAgg::justifyHead(vec<Lit>& just){
	if(lower){
		int bestpos = currentbestpossible;
		for(vector<int>::size_type i=0; i<set->wlitset.size() && bestpos<=bound; i++){
			if(litvalue[i]==l_Undef){
				bestpos -= set->wlitset[i].weight;
				just.push(~set->wlitset[i].lit);
			}else if(litvalue[i]==l_False){
				just.push(~set->wlitset[i].lit);
			}
		}
	}else{
		if(currentbestpossible < bound){ assert(false); } //not justifiable
		else if(currentbestcertain >= bound){
			for(int i=0; i<stack.size(); i++){
				if(stack[i].type==POS && stack[i].wlit.weight<=bound){
					just.push(stack[i].wlit.lit);
					break;
				}
			}
		}else{
			int sum = currentbestcertain;
			for(vector<int>::size_type i=0; sum<bound && i<set->wlitset.size(); i++){
				if(litvalue[i]!=l_False){
					sum += set->wlitset[i].weight;
					just.push(set->wlitset[i].lit);
				}
			}
			assert(sum>=bound);
		}
	}
}

/**
 * Add all literals not in the unfounded set to the loopformula
 */
void MinAgg::createLoopFormula(const std::set<Var>& ufs, vec<Lit>& loopf, vec<int>& seen){
	vector<WLit> lits = set->wlitset;
	if(lower){
		for (vector<int>::size_type i=0; i<lits.size() && lits[i].weight <= bound; ++i) {
			if (ufs.find(var(lits[i].lit)) == ufs.end()) {
				loopf.push(lits[i].lit);
				seen[var(lits[i].lit)] = (sign(lits[i].lit) ? 1 : 2);
			}
		}
	}else{
		for (vector<int>::size_type i=0; i<lits.size() && lits[i].weight < bound; ++i) {
			if (ufs.find(var(lits[i].lit)) == ufs.end()) {
				loopf.push(~lits[i].lit);
				seen[var(lits[i].lit)] = (sign(lits[i].lit) ? 2 : 1);
			}
		}
	}
}

void MaxAgg::createLoopFormula(const std::set<Var>& ufs, vec<Lit>& loopf, vec<int>& seen){
	vector<WLit> lits = set->wlitset;
	if(lower){
		for (vector<int>::size_type i=lits.size()-1; i>0 && lits[i].weight > bound; --i) {
			if (ufs.find(var(lits[i].lit)) == ufs.end()) {
				loopf.push(~lits[i].lit);
				seen[var(lits[i].lit)] = (sign(lits[i].lit) ? 2 : 1);
			}
		}
	}else{
		for (vector<int>::size_type i=lits.size()-1; i>0 && lits[i].weight >= bound; --i) {
			if (ufs.find(var(lits[i].lit)) == ufs.end()) {
				loopf.push(lits[i].lit);
				seen[var(lits[i].lit)] = (sign(lits[i].lit) ? 1 : 2);
			}
		}
	}
}

/**
 * TODO Geen idee wat hier nuttig aan is van loop formula, toch zeker niet om loops te vermijden?
 */
void SPAgg::createLoopFormula(const std::set<Var>& ufs, vec<Lit>& loopf, vec<int>& seen){
	for (vector<int>::size_type i = 0; i < set->wlitset.size(); ++i) {
		Lit l = set->wlitset[i].lit;
		if (litvalue[i] == l_True) {
			if (sign(l) || ufs.find(var(l)) == ufs.end()) {
				loopf.push(l);
				seen[var(l)] = (sign(l) ? 1 : 2);
			}
		} else if (litvalue[i] == l_False) {
			if (~sign(l) || ufs.find(var(l)) == ufs.end()) {
				loopf.push(~l);
				seen[var(l)] = (sign(l) ? 2 : 1);
			}
		}
	}
}

/**
 * AGG <= B: v is justified if one literal below/eq the bound is.
 * 					if so, change the justification to the literal
 * 					otherwise, add all nonfalse, non-justified, relevant, below the bound literals to the queue
 * A <= AGG: v is justified if the negation of all literals below the bound are. The emptyset is always a solution,
 * 			 so no conclusions have to be drawn from the literals above/eq the bound
 * 					if so, change the justification to the negation of all those below the bound literals
 * 					otherwise, add all nonfalse, non-justified, relevant, below the bound literals to the queue
 */
bool MinAgg::directlyJustifiable(Var v, std::set<Var>& ufs, Queue<Var>& q, vec<Lit>& j, vec<int>& seen, const vec<int>& scc){
	vector<WLit> lits = set->wlitset;
	bool justified = false;
	vec<Var> notjustified;	//all literals that are not justified
	vec<Lit> justification;	//the literals that form the justification. This is not a valid justification if notjustified.size>0
	if(lower){
		for (vector<int>::size_type i=0; lits[i].weight<=bound; ++i) {
			Lit l = lits[i].lit;
			if (seen[var(l)]!=0 && scc[v]==scc[var(l)] && ufs.find(var(l)) == ufs.end()){
				notjustified.push(var(l));
			}else{
				justification.push(l);
				justified = true;
			}
		}
	}else{
		for (vector<int>::size_type i=0; lits[i].weight<bound; ++i) {
			Lit l = lits[i].lit;
			justification.push(~l); //push negative literal, because it should become false
			//FIXME de signs die hier stonden, zijn die noodzakelijk?
			if (seen[var(l)]!=0 && scc[v]==scc[var(l)] && ufs.find(var(l)) == ufs.end()){
				notjustified.push(var(l));
			}
		}
		if (notjustified.size()==0) {
			justified = true;
		}
	}
	if (justified) {
		justification.copyTo(j);
	}else{
		for (int i=0; i<notjustified.size(); ++i) {
			std::pair<std::set<Var>::iterator, bool> pr = ufs.insert(notjustified[i]);
			if (pr.second){
				q.insert(notjustified[i]);
			}
		}
	}
	return justified;
}

bool MaxAgg::directlyJustifiable(Var v, std::set<Var>& ufs, Queue<Var>& q, vec<Lit>& j, vec<int>& seen, const vec<int>& scc){
	vector<WLit> lits = set->wlitset;
	bool justified = false;
	vec<Var> notjustified;	//all literals that are not justified
	vec<Lit> justification;	//the literals that form the justification. This is not a valid justification if notjustified.size>0
	if(lower){
		for (vector<int>::size_type i=lits.size()-1; lits[i].weight>bound; i--) {
			Lit l = lits[i].lit;
			justification.push(~l); //push negative literal, because it should become false
			if (seen[var(l)]!=0 && scc[v]==scc[var(l)] && ufs.find(var(l)) == ufs.end()){
				notjustified.push(var(l));
			}
		}
		if(notjustified.size()==0){
			justified = true;
		}
	}else{
		for (vector<int>::size_type i=lits.size()-1; lits[i].weight>=bound; i--) {
			Lit l = lits[i].lit;
			if (seen[var(l)]!=0 && scc[v]==scc[var(l)] && ufs.find(var(l)) == ufs.end()){
				notjustified.push(var(l));
			}else{
				justification.push(l);
				justified = true;
			}
		}
	}
	if (justified) {
		justification.copyTo(j);
	}else{
		for (int i=0; i<notjustified.size(); ++i) {
			std::pair<std::set<Var>::iterator, bool> pr = ufs.insert(notjustified[i]);
			if (pr.second){
				q.insert(notjustified[i]);
			}
		}
	}
	return justified;
}

/**
 * AGG <= B: add a number of justified, nontrue literals such that they guarantee the bestpossible value is below the bound
 * A <= AGG: need a justification of which the sum exceed/eq the bound
 */
bool SPAgg::directlyJustifiable(Var v, std::set<Var>& ufs, Queue<Var>& q, vec<Lit>& j, vec<int>& seen, const vec<int>& scc){
	vector<WLit> lits = set->wlitset;
	bool justified = false;
	vec<Var> notjustified;	//all atoms that are not justified
	vec<Lit> justification;
	if(lower){
		int bestpossible = getBestPossible();
		for (vector<int>::size_type i = 0; !justified && i < lits.size(); ++i) {
			Lit l = lits[i].lit;
			if (litvalue[i] != l_True) {
				if (seen[var(l)]!=0 && scc[v]==scc[var(l)] && ufs.find(var(l)) == ufs.end()) {
					notjustified.push(var(l));
				} else {
					justification.push(~l);
					if(sum){
						bestpossible -= lits[i].weight;
					}else{
						bestpossible /= lits[i].weight;
					}
					if (bestpossible <= bound){
						justified = true;
					}
				}
			}
		}
	}else{
		int bestcertain = emptysetValue;
		for (vector<int>::size_type i = 0; !justified && i < lits.size(); ++i) {
			Lit l = lits[i].lit;
			if (litvalue[i] != l_False) {
				if (seen[var(l)]!=0 && scc[v]==scc[var(l)] && ufs.find(var(l)) == ufs.end()) {
					notjustified.push(var(l));
				} else {
					justification.push(l);
					if(sum){
						bestcertain += lits[i].weight;
					}else{
						bestcertain *= lits[i].weight;
					}
					if (bestcertain >= bound){
						justified = true;
					}
				}
			}
		}
	}
	if(justified){
		justification.copyTo(j);
	}else{
		for (int i=0; i<notjustified.size(); ++i) {
			std::pair<std::set<Var>::iterator, bool> pr = ufs.insert(notjustified[i]);
			if (pr.second){
				q.insert(notjustified[i]);
			}
		}
	}
	return justified;
}
