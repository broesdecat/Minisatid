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

	setcopy[index] = l_Undef;
	if (pi.type == POS) {
		removeFromCertainSet(pi.wlit);
	}else{
		addToPossibleSet(pi.wlit);
	}
}

lbool Agg::canPropagateHead(){
	if ((lower && currentbestcertain > bound) || (!lower && currentbestpossible < bound)) {
		return l_False;
	} else if ((lower && currentbestpossible <= bound) || (!lower && currentbestcertain >= bound)) {
		return l_True;
	} else {
		return l_Undef;
	}
}

Clause* Agg::propagate(Lit p, AggrWatch& ws){
	Clause* confl = NULL;

	Occurrence tp = relativeOccurrence(ws.type, p);
	stack.push(PropagationInfo(p, set->wlitset[ws.index].weight,tp));
	if (tp == HEAD){ // The head literal has been propagated
		if(headvalue!=l_Undef){
			assert(false); //TODO check if this can never occur
		}else{
			headvalue = sign(p)?l_False:l_True;
		}
		confl = propagate(!sign(p));
	}else { // It's a set literal.
		setcopy[ws.index] = tp==POS?l_True:l_False;
		tp==POS? addToCertainSet(set->wlitset[ws.index]):removeFromPossibleSet(set->wlitset[ws.index]);

		lbool result = canPropagateHead();
		if(result==l_True){
			confl = AggSolver::aggsolver->aggrEnqueue(head, new AggrReason(this, HEAD));
		}else if(result==l_False){
			confl = AggSolver::aggsolver->aggrEnqueue(~head, new AggrReason(this, HEAD));
		}else if(headvalue != l_Undef){
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
 * Checks whether the same literal occurs multiple times in the set-> If this is the case, all identical literals are combined into one.
 * How the weights are combined depends on the aggregate type, and the combination is made by the method getCombinedWeight.
 * For this reason, the method cannot be called in the constructor of Agg (because the subtype has not been constructed yet.
 */
void Agg::doSetReduction() {
	vector<WLit> oldset = set->wlitset;
	std::sort(oldset.begin(), oldset.end(), compareLits);

	AggrSet* newset = new AggrSet();
	int indexinnew = 0;
	newset->wlitset.push_back(oldset[indexinnew]);

	bool setisreduced = false;
	for(vector<int>::size_type i=1; i<oldset.size(); i++){
		WLit old = newset->wlitset[indexinnew];
		WLit newl = oldset[i];
		if(var(old.lit)==var(newl.lit)){
			setisreduced = true;
			if(old.lit==newl.lit){
				//same literal, only keep best one
				newset->wlitset[newset->wlitset.size()-1].weight = getCombinedWeight(newl.weight, old.weight);
			}else{
				WLit l = handleOccurenceOfBothSigns(old, newl);
				newset->wlitset.pop_back();
				newset->wlitset.push_back(l);
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

int MinAgg::getBestPossible() {
	int min = emptysetValue;
	for (vector<Lit>::size_type j = 0; j < set->wlitset.size(); j++) {
		if(min > set->wlitset[j].weight){
			min = set->wlitset[j].weight;
		}
	}
	return min;
}

MinAgg::~MinAgg() {
}

//OVERRIDDEN BECAUSE BEST IS LOWER THAN WORST
lbool MinAgg::canPropagateHead() {
	if ((lower && currentbestpossible > bound) || (!lower && currentbestcertain < bound)) {
		return l_False;
	} else if ((lower && currentbestcertain <= bound) || (!lower && currentbestpossible >= bound)) {
		return l_True;
	} else {
		return l_Undef;
	}
}

void MinAgg::removeFromCertainSet(WLit l){
	truecount--;
	if (truecount == 0) {
		currentbestcertain = emptysetValue;
	}else{
		if(l.weight==currentbestcertain){
			currentbestcertain = emptysetValue;
			for(int i=0; i<stack.size(); i++){
				if(stack[i].type==POS && currentbestcertain>stack[i].wlit.weight){
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
				if(setcopy[i] != l_False && currentbestpossible > set->wlitset[i].weight){
					currentbestpossible = set->wlitset[i].weight;
				}
			}
		}
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
 * If the head is true && A <= AGG, make all literals false that have a weight smaller than the bound (because that would make the aggregate false)
 * If the head is false && AGG <= B, make all literals false that have a weight smaller than the bound (because that would make the aggregate false)
 */
Clause* MinAgg::propagate(bool headtrue) {
	Clause* confl = NULL;
	if ((headtrue && !lower) || (!headtrue && lower)) {
		for (vector<Lit>::size_type i = 0; confl == NULL && i < set->wlitset.size(); i++) {
			if (set->wlitset[i].weight < bound) {
				confl = AggSolver::aggsolver->aggrEnqueue(~set->wlitset[i].lit, new AggrReason(this, NEG));
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
				if(setcopy[i] != l_False && currentbestpossible < set->wlitset[i].weight){
					currentbestpossible = set->wlitset[i].weight;
				}
			}
		}
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
 * If the head is true && AGG <= B, make all literals false that have a weight higher than the bound (because that would make the aggregate false)
 * If the head is false && A <= AGG, make all literals false that have a weight higher than the bound (because that would make the aggregate false)
 */
Clause* MaxAgg::propagate(bool headtrue) {
	Clause* confl = NULL;
	if ((headtrue && lower) || (!headtrue && !lower)) {
		for (vector<Lit>::size_type i = 0; confl == NULL && i < set->wlitset.size(); i++) {
			if (set->wlitset[i].weight > bound) {
				confl = AggSolver::aggsolver->aggrEnqueue(~set->wlitset[i].lit, new AggrReason(this, NEG));
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

int	SPAgg::getCombinedWeight(int first, int second){
	if(sum){
		return first+second;
	}else{
		return first*second;
	}
}

WLit SPAgg::handleOccurenceOfBothSigns(WLit one, WLit two){
	if(!sum){
		reportf("Product aggregates in which both the literal and its negation occur "
				"are currently not supported. Replace %s%d or %s%d by a tsietin.\n",
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
Clause* SPAgg::propagate(bool headtrue){
	Clause* c = NULL;
	vector<WLit>::iterator pos;

	if (headtrue) {
		if(lower){
			int weightbound;
			if(sum){
				weightbound = bound-currentbestcertain;
			}else{
				//currentbestcertain = 0 not possible (always leq 1)
				weightbound = bound/currentbestcertain;
			}
			//+1 because larger and not eq
			pos = lower_bound(set->wlitset.begin(), set->wlitset.end(), weightbound+1);
		}else{
			int weightbound;
			if(sum){
				weightbound = currentbestpossible-bound;
			}else{
				//if bound == 0, it is never possible to obtain a smaller product, so get first weight larger than 0
				weightbound = bound==0?0:currentbestpossible/bound;
			}
			//+1 because larger and not eq
			pos = lower_bound(set->wlitset.begin(), set->wlitset.end(), weightbound+1);
		}
	} else {
		if(lower){
			int weightbound;
			if(sum){
				weightbound = currentbestpossible - bound;
			}else{
				//if bound == 0, it is never possible to obtain a smaller product, so get first weight larger than 0
				weightbound = bound==0?0:currentbestpossible/bound;
			}
			pos = lower_bound(set->wlitset.begin(), set->wlitset.end(), weightbound);
		}else{
			int weightbound;
			if(sum){
				weightbound = bound - currentbestcertain;
			}else{
				//currentbestcertain = 0 not possible (always leq 1)
				weightbound = bound/currentbestcertain;
			}
			pos = lower_bound(set->wlitset.begin(), set->wlitset.end(), weightbound);
		}
	}
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
		if (setcopy[u]==l_Undef) {// no conflicts possible (because setting an unknown literal
			if((lower && headtrue) || (!lower && !headtrue)){
				c = AggSolver::aggsolver->aggrEnqueue(~set->wlitset[u].lit, new AggrReason(this, NEG));
			}else{
				c = AggSolver::aggsolver->aggrEnqueue(set->wlitset[u].lit, new AggrReason(this, POS));
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
void MinAgg::getExplanation(Lit p, vec<Lit>& lits, int p_idx, AggrReason& ar){
	if (ar.type == HEAD) {
		if (ar.expr->head == p) {
			if(lower){
				for(int i=0; i<stack.size(); i++){
					if(stack[i].wlit.weight<=bound && stack[i].type==POS){
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
					if(stack[i].wlit.weight<bound && stack[i].type==POS){
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
void MaxAgg::getExplanation(Lit p, vec<Lit>& lits, int p_idx, AggrReason& ar){
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
					if(stack[i].wlit.weight>=bound && stack[i].type==POS){
						lits.push(~stack[i].wlit.lit);
						break;
					}
				}
			}
		} else {
			if(lower){
				for(int i=0; i<stack.size(); i++){
					if(stack[i].wlit.weight>bound && stack[i].type==POS){
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
void SPAgg::getExplanation(Lit p, vec<Lit>& lits, int p_idx, AggrReason& ar){
	int possiblesum, certainsum;
	certainsum = emptysetValue;
	possiblesum = getBestPossible();

	if(ar.type == POS){
		if(sum){
			possiblesum -= set->wlitset[p_idx].weight;
		}else{
			possiblesum /= set->wlitset[p_idx].weight;
		}

	}else if(ar.type == NEG){
		if(sum){
			certainsum += set->wlitset[p_idx].weight;
		}else{
			certainsum *= set->wlitset[p_idx].weight;
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

//FIXME ik denk dat de huidige implementatie van propagatejustifications nog niet correct is

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
					if(setcopy[i]==l_Undef){
						bestposs -= set->wlitset[i].weight;
					}
					jstf.push(set->wlitset[i].lit);
				}
			}
			if(bestposs>bound){
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
			int sum = emptysetValue;
			for(vector<int>::size_type i=0; i<set->wlitset.size(); i++){
				if(nb_body_lits_to_justify[var(set->wlitset[i].lit)] == 0 && setcopy[i] != l_False){
					jstf.push(set->wlitset[i].lit);
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
 * @pre: v is not false, so a justification exists (TODO is this a correct precondition? It supposes that all possible propagations have been done?)
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
				if(stack[i].wlit.weight<=bound && stack[i].type==POS){
					just.push(stack[i].wlit.lit);
					break;
				}
			}
		}else{
			for(vector<int>::size_type i=0; i<set->wlitset.size(); i++){
				if(setcopy[i]!=l_False && set->wlitset[i].weight<=bound){
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
				if(stack[i].wlit.weight<=bound && stack[i].type==POS){
					just.push(stack[i].wlit.lit);
					break;
				}
			}
		}else{
			for(vector<int>::size_type i=0; i<set->wlitset.size(); i++){
				if(setcopy[i]!=l_False && set->wlitset[i].weight>=bound){
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
			if(setcopy[i]==l_Undef){
				bestpos -= set->wlitset[i].weight;
				just.push(~set->wlitset[i].lit);
			}else if(setcopy[i]==l_False){
				just.push(~set->wlitset[i].lit);
			}
		}
	}else{
		if(currentbestpossible < bound){ assert(false); } //not justifiable
		else if(currentbestcertain >= bound){
			for(int i=0; i<stack.size(); i++){
				if(stack[i].wlit.weight<=bound && stack[i].type==POS){
					just.push(stack[i].wlit.lit);
					break;
				}
			}
		}else{
			int sum = currentbestcertain;
			for(vector<int>::size_type i=0; sum<bound && i<set->wlitset.size(); i++){
				if(setcopy[i]!=l_False){
					sum += set->wlitset[i].weight;
					just.push(set->wlitset[i].lit);
				}
			}
			assert(sum>=bound);
		}
	}
}
