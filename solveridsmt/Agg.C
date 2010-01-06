#include "Agg.h"
#include "AggSolver.h"

lbool Agg::value(Lit p) {
	return AggSolver::aggsolver->value(p);
}

void Agg::backtrack(WLit l, bool wasinset) {
	if (wasinset) {
		truecount--;
		if (truecount == 0) {
			currentworst = emptysetValue;
		}
	}
	//FIXME: hier een update methode voor maken ipv alles opnieuw te berekenen
	currentworst = getCurrentBestCertain();
	currentbest = getCurrentBestPossible();
}

void Agg::initialize() {
	currentbest = getCurrentBestPossible(true);
	currentworst = emptysetValue;
}

lbool Agg::updateAndCheckPropagate(WLit l, bool addtoset) {
	//update values
	if (addtoset) {
		truecount++;
	}
	//FIXME: hier een update methode voor maken ipv alles opnieuw te berekenen
	currentworst = getCurrentBestCertain();
	currentbest = getCurrentBestPossible();

	//check if propagation possible
	if ((lower && currentworst > bound) || (!lower && currentbest < bound)) {
		return l_False;
	} else if ((lower && currentbest <= bound) || (!lower && currentworst >= bound)) {
		return l_True;
	} else {
		return l_Undef;
	}
}

int MinAgg::getCurrentBestPossible(bool alltimebest) {
	int min = emptysetValue;

	if(alltimebest){
		for (int j = 0; j < set.wlitset.size(); j++) {
			if(min > set.wlitset[j].weight){
				min = set.wlitset[j].weight;
			}
		}
	}else{
		//FIXME really not optimal
		for(int i=0; i<set.wlitset.size(); i++){
			Lit l = set.wlitset[i].lit;
			int weight = set.wlitset[i].weight;
			bool invalid = false;
			for (int j = 0; j < stack.size(); j++) {
				if(stack[j].wlit.lit==~l){
					invalid = true;
					break;
				}
			}
			if (!invalid && min > weight) {
				min = weight;
			}
		}
	}
	return min;
}

int MinAgg::getCurrentBestCertain() {
	int min = emptysetValue;

	for(int i=0; i<set.wlitset.size(); i++){
		Lit l = set.wlitset[i].lit;
		int weight = set.wlitset[i].weight;
		bool invalid = true;
		for (int j = 0; j < stack.size(); j++) {
			if(stack[j].wlit.lit==l){
				invalid = false;
				break;
			}
		}
		if (!invalid && min > weight) {
			min = weight;
		}
	}

	return min;
}

MinAgg::~MinAgg() {
}

//OVERRIDDEN BECAUSE BEST IS LOWER THAN WORST
lbool MinAgg::updateAndCheckPropagate(WLit l, bool addtoset) {
	//update values
	if (addtoset) {
		truecount++;
	}

	//FIXME: hier een update methode voor maken ipv alles opnieuw te berekenen
	//maar goed opletten want snel fouten (na backtrack enzo
	currentworst = getCurrentBestCertain();
	currentbest = getCurrentBestPossible();

	//printf("currentbest: %d, currentworst:%d\n", currentbest, currentworst);

	//check if propagation possible
	if ((lower && currentbest > bound) || (!lower && currentworst < bound)) {
		return l_False;
	} else if ((lower && currentworst <= bound) || (!lower && currentbest >= bound)) {
		return l_True;
	} else {
		return l_Undef;
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

int MaxAgg::getCurrentBestPossible(bool alltimebest) {
	int max = emptysetValue;

	if(alltimebest){
		for (int j = 0; j < set.wlitset.size(); j++) {
			if(max < set.wlitset[j].weight){
				max = set.wlitset[j].weight;
			}
		}
	}else{
		for(int i=0; i<set.wlitset.size(); i++){
			Lit l = set.wlitset[i].lit;
			int weight = set.wlitset[i].weight;
			bool invalid = false;
			for (int j = 0; j < stack.size(); j++) {
				if(stack[j].wlit.lit==~l){
					invalid = true;
					break;
				}
			}
			if (!invalid && max < weight) {
				max = weight;
			}
		}
	}

	return max;
}

int MaxAgg::getCurrentBestCertain() {
	int max = emptysetValue;

	for(int i=0; i<set.wlitset.size(); i++){
		Lit l = set.wlitset[i].lit;
		int weight = set.wlitset[i].weight;
		bool invalid = true;
		for (int j = 0; j < stack.size(); j++) {
			if(stack[j].wlit.lit==l){
				invalid = false;
				break;
			}
		}
		if (!invalid && max < weight) {
			max = weight;
		}
	}

	return max;
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

/*****************
 * SUM AGGREGATE *
 *****************/

SumAgg::~SumAgg() {
}

int SumAgg::getCurrentBestPossible(bool alltimebest) {
	int max = emptysetValue;

	if(alltimebest){
		for (int j = 0; j < set.wlitset.size(); j++) {
			max += set.wlitset[j].weight;
		}
	}else{
		for(int i=0; i<set.wlitset.size(); i++){
			Lit l = set.wlitset[i].lit;
			int weight = set.wlitset[i].weight;
			bool invalid = false;
			for (int j = 0; j < stack.size(); j++) {
				if(stack[j].wlit.lit==~l){
					invalid = true;
					break;
				}
			}
			if (!invalid) {
				max += weight;
			}
		}
	}

	return max;
}

int SumAgg::getCurrentBestCertain() {
	int max = emptysetValue;

	for(int i=0; i<set.wlitset.size(); i++){
		Lit l = set.wlitset[i].lit;
		int weight = set.wlitset[i].weight;
		bool invalid = true;
		for (int j = 0; j < stack.size(); j++) {
			if(stack[j].wlit.lit==l){
				invalid = false;
				break;
			}
		}
		if (!invalid) {
			max += weight;
		}
	}

	return max;
}

/**
 * If head is true, and making a literal true would increase the bestcertain value above the bound (and lEQ)
 * 					or  making a literal false would decrease the bestpossible below the bound (and gEQ)
 * 		then make that literal and all higher ones (in weight) false (resp. true)
 *
 * If head is false, and making a literal false would decrease the bestcertain below the bound (and lEQ)
 * 					 or making a literal true would increase the bestpossible above the bound (and gEQ)
 * 		then make that literal and all higher ones (in weight) true (resp. false)
 */
Clause* SumAgg::propagate(bool headtrue) {
	if (headtrue) {
		bool foundhighweight = false;
		for (int u = 0; u < set.wlitset.size(); u++) {
			if (value(set.wlitset[u].lit) == l_Undef) {// no conflict possible
				if ((lower && currentworst + set.wlitset[u].weight > bound)
						||
					(!lower && currentbest - set.wlitset[u].weight < bound)){
					foundhighweight = true;
				}
				if(foundhighweight){
					if(lower){
						AggSolver::aggsolver->aggrEnqueue(~set.wlitset[u].lit, new AggrReason(*this, NEG));
					}else{
						AggSolver::aggsolver->aggrEnqueue(set.wlitset[u].lit, new AggrReason(*this, POS));
					}
				}
			}
		}
	} else {
		bool foundhighweight = false;
		for (int u = 0; u < set.wlitset.size(); u++) {
			if (value(set.wlitset[u].lit) == l_Undef) {
				if ((lower && currentbest - set.wlitset[u].weight <= bound)
						||
					(!lower && currentworst+set.wlitset[u].weight >=bound)) {
					foundhighweight = true;
				}
				if(foundhighweight){
					if(lower){
						AggSolver::aggsolver->aggrEnqueue(set.wlitset[u].lit, new AggrReason(*this, POS));
					}else{
						AggSolver::aggsolver->aggrEnqueue(~set.wlitset[u].lit, new AggrReason(*this, NEG));
					}
				}
			}
		}
	}
	return NULL;
}

/*********************
 * PRODUCT AGGREGATE *
 *********************/

ProdAgg::~ProdAgg() {
}

int ProdAgg::getCurrentBestPossible(bool alltimebest) {
	int max = emptysetValue;

	if(alltimebest){
		for (int j = 0; j < set.wlitset.size(); j++) {
			max += set.wlitset[j].weight;
		}
	}else{
		for(int i=0; i<set.wlitset.size(); i++){
			Lit l = set.wlitset[i].lit;
			int weight = set.wlitset[i].weight;
			bool invalid = false;
			for (int j = 0; j < stack.size(); j++) {
				if(stack[j].wlit.lit==~l){
					invalid = true;
					break;
				}
			}
			if (!invalid) {
				max *= weight;
			}
		}
	}

	return max;
}

int ProdAgg::getCurrentBestCertain() {
	int max = emptysetValue;

	for(int i=0; i<set.wlitset.size(); i++){
		Lit l = set.wlitset[i].lit;
		int weight = set.wlitset[i].weight;
		bool invalid = true;
		for (int j = 0; j < stack.size(); j++) {
			if(stack[j].wlit.lit==l){
				invalid = false;
				break;
			}
		}
		if (!invalid) {
			max *= weight;
		}
	}

	return max;
}

Clause* ProdAgg::propagate(bool headtrue) {
	//FIXME
	/*if (value(ae.c) == l_True) {
	 for (int u = 0; u < as.set.size(); u++) {
	 if (value(as.set[u].lit) == l_Undef) {
	 if (as.min * as.set[u].weight > ae.max)
	 aggrEnqueue(~as.set[u].lit, new AggrReason(&ae, &as,
	 NEG));
	 else if (as.max / as.set[u].weight < ae.min)
	 aggrEnqueue(as.set[u].lit,
	 new AggrReason(&ae, &as, POS));
	 }
	 }
	 } else if (value(ae.c) == l_False) {
	 if (as.min >= ae.min || as.max <= ae.max) {
	 int minw = 2147483647;
	 for (int u = 0; u < as.set.size(); u++)
	 if (value(as.set[u].lit) == l_Undef && as.set[u].weight
	 < minw)
	 minw = as.set[u].weight;
	 bool maketrue = minw != 2147483647 && as.min >= ae.min
	 && as.max / minw <= ae.max;
	 bool makefalse = minw != 2147483647 && as.max <= ae.max
	 && as.min * minw >= ae.min;
	 if (maketrue)
	 for (int u = 0; u < as.set.size(); u++)
	 if (value(as.set[u].lit) == l_Undef)
	 aggrEnqueue(as.set[u].lit, new AggrReason(&ae, &as,
	 POS));
	 if (makefalse)
	 for (int u = 0; u < as.set.size(); u++)
	 if (value(as.set[u].lit) == l_Undef)
	 aggrEnqueue(~as.set[u].lit, new AggrReason(&ae,
	 &as, NEG));
	 }
	 }*/
	return NULL;
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
void SumAgg::getExplanation(Lit p, vec<Lit>& lits, int p_idx, AggrReason& ar){
	int possiblesum, certainsum;
	certainsum = emptysetValue;
	possiblesum = getCurrentBestPossible(true);

	lbool headValue = AggSolver::aggsolver->value(head);
	if(ar.type == POS || ar.type == NEG){
		lits.push(headValue==l_True?~head:head);
	}

	if(ar.type == POS){
		possiblesum -= set.wlitset[p_idx].weight;
	}else if(ar.type == NEG){
		certainsum += set.wlitset[p_idx].weight;
	}

	//an explanation can exist without any other set literals, so check for this
	if(ar.type==NEG && ((lower && certainsum > bound) || (!lower && certainsum >= bound))){
		return;
	}
	if(ar.type==POS && ((lower && possiblesum <= bound) || (!lower && possiblesum < bound))){
		return;
	}

	bool derived = false, fullyexplained = false;
	for(int i=0; !fullyexplained && i<stack.size() && stack[i].wlit.lit!=p; i++){
		if(stack[i].type == POS){ //means that the literal in the set became true
			certainsum += stack[i].wlit.weight;

			if(ar.type==HEAD){
				if(head==p && !lower){
					lits.push(~stack[i].wlit.lit);
					if(bound <= certainsum){
						fullyexplained = true;
					}
				}else if(head==~p && lower){
					lits.push(~stack[i].wlit.lit);
					if(bound < certainsum){
						fullyexplained = true;
					}
				}
			}else if(ar.type==NEG){
				lits.push(~stack[i].wlit.lit);
				if((lower && certainsum > bound) || (!lower && certainsum >= bound)){
					fullyexplained = true;
				}
			}
		}else if(stack[i].type == NEG){ //the literal in the set became false
			possiblesum -= stack[i].wlit.weight;

			if(ar.type==HEAD){
				if(head==p && lower){
					lits.push(~stack[i].wlit.lit);
					if(possiblesum <= bound){
						fullyexplained = true;
					}
				}else if(head==~p && !lower){
					lits.push(~stack[i].wlit.lit);
					if(possiblesum < bound){
						fullyexplained = true;
					}
				}
			}else if(ar.type==POS){
				lits.push(~stack[i].wlit.lit);
				if((lower && possiblesum <= bound) || (!lower && possiblesum < bound)){
					fullyexplained = true;
				}
			}
		}else{
			//head derived, can only happen once
			assert(!derived);
			derived = true;
		}
	}
	assert(fullyexplained);
}

void ProdAgg::getExplanation(Lit p, vec<Lit>& lits, int p_idx, AggrReason& ar){
	/*int cmax = ar.expr.set.headmax;
	int min_needed = 1;
	int max_needed = cmax;
	if (ar.type == HEAD) {
		// [mn >= i && mx =< j  ==>  c]  OR  [mn > j  || mx < i  ==>  ~c]
		if (ar.expr.head == p) {
			min_needed = ar.expr.min;
			max_needed = ar.expr.max;
		} else {
			assert(ar.expr.head==~p);
			if (ar.expr.set.min > ar.expr.max)
				min_needed = ar.expr.max + 1;
			else
				max_needed = ar.expr.min - 1;
		}
	} else if (ar.type == POS) {
		// c is true && mx = i  OR  c is false && mn >= i && mx = j+1
		if (value(ar.expr.head) == l_True) {
			lits.push(~ar.expr.head);
			max_needed = ar.expr.min + ar.expr.set.wlitset[p_idx].weight - 1;
		} else {
			assert(value(ar.expr.head)==l_False);
			lits.push(ar.expr.head);
			min_needed = ar.expr.min;
			max_needed = ar.expr.max + ar.expr.set.wlitset[p_idx].weight;
		}
	} else {
		assert(ar.type==NEG);
		// c is true && mn = j  OR  c is false && mx =< j && mn = i-1
		if (value(ar.expr.head) == l_True) {
			lits.push(~ar.expr.head);
			min_needed = ar.expr.max - ar.expr.set.wlitset[p_idx].weight + 1;
		} else {
			assert(value(ar.expr.head)==l_False);
			lits.push(ar.expr.head);
			min_needed = ar.expr.min - ar.expr.set.wlitset[p_idx].weight;
			max_needed = ar.expr.max;
		}
	}

//		 We now walk over the stack and add literals that are relevant to the
//		 reason clause, until it is big enough. When that is depends on the type
//		 of propagation that was done to derive p.
//
	Lit q;
	char t;
	for (int i = 0; min_needed + (cmax - max_needed)
			> (ar.expr.set.type == SUM ? 0 : 1); i++) {
		q = ar.expr.set.stack[i].lit;
		assert(q!=p); // We should have assembled a reason clause before encountering this.
		t = ar.expr.set.stack[i].type;

		// if (t==0) then q is irrelevant to this derivation.
		if (t == 1 && min_needed > (ar.expr.set.type == SUM ? 0 : 1)) {
			lits.push(~q);
			min_needed = min_needed / ar.expr.set.stack[i].weight
							+ (min_needed % ar.expr.set.stack[i].weight == 0 ? 0	: 1);
		} else if (t == 2 && max_needed < cmax) {
			lits.push(~q);
			max_needed *= ar.expr.set.stack[i].weight;
		}
	}*/
}


/*****************
 * PRINT METHODS *
 *****************/

void Agg::printAgg(const char* name) const{
	AggSolver::aggsolver->printLit(head);
	if(lower){
		reportf(" <- %s{", name);
	}else{
		reportf(" <- %d <= %s{", bound, name);
	}
	AggSolver::aggsolver->printAggrSet(set);
	if(lower){
		reportf(" } <= %d. Known values: min=%d, max=%d\n", bound, currentworst, currentbest);
	}else{
		reportf(" }. Known values: min=%d, max=%d\n", currentworst, currentbest);
	}
}

void MinAgg::print() const{
	printAgg("MIN");
}

void MaxAgg::print() const{
	printAgg("MAX");
}

void SumAgg::print() const{
	printAgg("SUM");
}

void ProdAgg::print() const{
	printAgg("PROD");
}
