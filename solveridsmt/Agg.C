#include "Agg.h"
#include "AggSolver.h"

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
	stack.push(PropagationInfo(p, set.wlitset[ws.index].weight,tp));
	if (tp == HEAD){ // The head literal has been propagated
		if(headvalue!=l_Undef){
			assert(false); //TODO check if this can never occur
		}else{
			headvalue = sign(p)?l_False:l_True;
		}
		confl = propagate(!sign(p));
	}else { // It's a set literal.
		setcopy[ws.index] = tp==POS?l_True:l_False;
		tp==POS? addToCertainSet(set.wlitset[ws.index]):removeFromPossibleSet(set.wlitset[ws.index]);

		lbool result = canPropagateHead();
		if(result==l_True){
			confl = AggSolver::aggsolver->aggrEnqueue(head, new AggrReason(*this, HEAD));
		}else if(result==l_False){
			confl = AggSolver::aggsolver->aggrEnqueue(~head, new AggrReason(*this, HEAD));
		}else if(headvalue != l_Undef){
			confl = propagate(headvalue==l_True);
		}
	}

	return confl;
}

void Agg::initialize() {
	currentbestpossible = getBestPossible();
	currentbestcertain = emptysetValue;
	possiblecount = set.wlitset.size();
}

int MinAgg::getBestPossible() {
	int min = emptysetValue;
	for (int j = 0; j < set.wlitset.size(); j++) {
		if(min > set.wlitset[j].weight){
			min = set.wlitset[j].weight;
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
			for(int i=0; i<set.wlitset.size(); i++){
				if(setcopy[i] != l_False && currentbestpossible > set.wlitset[i].weight){
					currentbestpossible = set.wlitset[i].weight;
				}
			}
		}
	}
}

/**
 * If the head is true && A <= AGG, make all literals false that have a weight smaller than the bound (because that would make the aggregate false)
 * If the head is false && AGG <= B, make all literals false that have a weight smaller than the bound (because that would make the aggregate false)
 */
Clause* MinAgg::propagate(bool headtrue) {
	Clause* confl = NULL;
	if ((headtrue && !lower) || (!headtrue && lower)) {
		for (int i = 0; confl == NULL && i < set.wlitset.size(); i++) {
			if (set.wlitset[i].weight < bound) {
				confl = AggSolver::aggsolver->aggrEnqueue(~set.wlitset[i].lit, new AggrReason(*this, NEG));
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

	for (int j = 0; j < set.wlitset.size(); j++) {
		if(max < set.wlitset[j].weight){
			max = set.wlitset[j].weight;
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
			for(int i=0; i<set.wlitset.size(); i++){
				if(setcopy[i] != l_False && currentbestpossible < set.wlitset[i].weight){
					currentbestpossible = set.wlitset[i].weight;
				}
			}
		}
	}
}

/**
 * If the head is true && AGG <= B, make all literals false that have a weight higher than the bound (because that would make the aggregate false)
 * If the head is false && A <= AGG, make all literals false that have a weight higher than the bound (because that would make the aggregate false)
 */
Clause* MaxAgg::propagate(bool headtrue) {
	Clause* confl = NULL;
	if ((headtrue && lower) || (!headtrue && !lower)) {
		for (int i = 0; confl == NULL && i < set.wlitset.size(); i++) {
			if (set.wlitset[i].weight > bound) {
				confl = AggSolver::aggsolver->aggrEnqueue(~set.wlitset[i].lit, new AggrReason(*this, NEG));
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
	for (int j = 0; j < set.wlitset.size(); j++) {
		if(sum){
			max += set.wlitset[j].weight;
		}else{
			max *= set.wlitset[j].weight;
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
 */
Clause* SPAgg::propagate(bool headtrue){
	Clause* c = NULL;
	if (headtrue) {
		bool foundhighweight = false;
		for (int u = 0; c==NULL && u < set.wlitset.size(); u++) {
			if (setcopy[u]==l_Undef) {// no conflicts possible (because setting an unknown literal
				if(sum){
					if ((lower && currentbestcertain + set.wlitset[u].weight > bound)
							||
						(!lower && currentbestpossible - set.wlitset[u].weight < bound)){
						foundhighweight = true;
					}
				}else{
					if ((lower && currentbestcertain * set.wlitset[u].weight > bound)
							||
						(!lower && currentbestpossible / set.wlitset[u].weight < bound)){
						foundhighweight = true;
					}
				}
				if(foundhighweight){
					if(lower){
						c = AggSolver::aggsolver->aggrEnqueue(~set.wlitset[u].lit, new AggrReason(*this, NEG));
					}else{
						c = AggSolver::aggsolver->aggrEnqueue(set.wlitset[u].lit, new AggrReason(*this, POS));
					}
				}
			}
		}
	} else {
		bool foundhighweight = false;
		for (int u = 0; u < set.wlitset.size(); u++) {
			if (setcopy[u]==l_Undef) { //again no conflicts possible
				if(sum){
					if ((lower && currentbestpossible - set.wlitset[u].weight <= bound)
							||
						(!lower && currentbestcertain+set.wlitset[u].weight >=bound)) {
						foundhighweight = true;
					}
				}else{
					if ((lower && currentbestpossible / set.wlitset[u].weight <= bound)
							||
						(!lower && currentbestcertain*set.wlitset[u].weight >=bound)) {
						foundhighweight = true;
					}
				}
				if(foundhighweight){
					if(lower){
						c = AggSolver::aggsolver->aggrEnqueue(set.wlitset[u].lit, new AggrReason(*this, POS));
					}else{
						c = AggSolver::aggsolver->aggrEnqueue(~set.wlitset[u].lit, new AggrReason(*this, NEG));
					}
				}
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
		if (ar.expr.head == p) {
			if(lower){
				for(int i=0; i<stack.size(); i++){
					if(stack[i].wlit.weight<=bound && stack[i].type==POS){
						lits.push(~stack[i].wlit.lit);
						break;
					}
				}
			}else{
				for(int i=0; i<set.wlitset.size() && set.wlitset[i].weight < bound; i++){
					lits.push(set.wlitset[i].lit);
				}
			}
		} else {
			if(lower){
				for(int i=0; i<set.wlitset.size() && set.wlitset[i].weight <= bound; i++){
					lits.push(set.wlitset[i].lit);
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
			for(int i=0; i<set.wlitset.size() && set.wlitset[i].weight<=bound; i++){
				if(set.wlitset[i].lit!=p){
					lits.push(set.wlitset[i].lit);
				}
			}
		}else{
			lits.push(head);
			for(int i=0; i<set.wlitset.size() && set.wlitset[i].weight<bound; i++){
				if(set.wlitset[i].lit!=p){
					lits.push(set.wlitset[i].lit);
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
		if (ar.expr.head == p) {
			if(lower){
				for(int i=0; i<set.wlitset.size(); i++){
					if(set.wlitset[i].weight > bound){
						lits.push(set.wlitset[i].lit);
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
				for(int i=0; i<set.wlitset.size(); i++){
					if(set.wlitset[i].weight >= bound){
						lits.push(set.wlitset[i].lit);
					}
				}
			}
		}
	} else if (ar.type == POS) {
		if(lower){
			lits.push(head);
			for(int i=0; i<set.wlitset.size(); i++){
				if(set.wlitset[i].weight>bound && set.wlitset[i].lit!=p){
					lits.push(set.wlitset[i].lit);
				}
			}
		}else{
			lits.push(~head);
			for(int i=0; i<set.wlitset.size(); i++){
				if(set.wlitset[i].weight>=bound && set.wlitset[i].lit!=p){
					lits.push(set.wlitset[i].lit);
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
			possiblesum -= set.wlitset[p_idx].weight;
		}else{
			possiblesum /= set.wlitset[p_idx].weight;
		}

	}else if(ar.type == NEG){
		if(sum){
			certainsum += set.wlitset[p_idx].weight;
		}else{
			certainsum *= set.wlitset[p_idx].weight;
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
