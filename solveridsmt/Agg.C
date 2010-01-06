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

/*********************
 * SUM-PRODUCT AGGREGATE *
 *********************/

SPAgg::~SPAgg() {
}

int SPAgg::getCurrentBestPossible(bool alltimebest) {
	int max = emptysetValue;

	if(alltimebest){
		for (int j = 0; j < set.wlitset.size(); j++) {
			if(sum){
				max += set.wlitset[j].weight;
			}else{
				max *= set.wlitset[j].weight;
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
			if (!invalid) {
				if(sum){
					max += weight;
				}else{
					max *= weight;
				}

			}
		}
	}

	return max;
}

int SPAgg::getCurrentBestCertain() {
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
			if(sum){
				max += weight;
			}else{
				max *= weight;
			}
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
Clause* SPAgg::propagate(bool headtrue){
	Clause* c = NULL;
	if (headtrue) {
		bool foundhighweight = false;
		for (int u = 0; c==NULL && u < set.wlitset.size(); u++) {
			if (value(set.wlitset[u].lit) == l_Undef) {// no conflict possible
				if(sum){
					if ((lower && currentworst + set.wlitset[u].weight > bound)
							||
						(!lower && currentbest - set.wlitset[u].weight < bound)){
						foundhighweight = true;
					}
				}else{
					if ((lower && currentworst * set.wlitset[u].weight > bound)
							||
						(!lower && currentbest / set.wlitset[u].weight < bound)){
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
			if (value(set.wlitset[u].lit) == l_Undef) {
				if(sum){
					if ((lower && currentbest - set.wlitset[u].weight <= bound)
							||
						(!lower && currentworst+set.wlitset[u].weight >=bound)) {
						foundhighweight = true;
					}
				}else{
					if ((lower && currentbest / set.wlitset[u].weight <= bound)
							||
						(!lower && currentworst*set.wlitset[u].weight >=bound)) {
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
	possiblesum = getCurrentBestPossible(true);

	lbool headValue = AggSolver::aggsolver->value(head);
	if(ar.type == POS || ar.type == NEG){
		lits.push(headValue==l_True?~head:head);
	}

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
			if(sum){
				certainsum += stack[i].wlit.weight;
			}else{
				certainsum *= stack[i].wlit.weight;
			}


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
			if(sum){
				possiblesum -= stack[i].wlit.weight;
			}else{
				possiblesum /= stack[i].wlit.weight;
			}


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

void SPAgg::print() const{
	if(sum){
		printAgg("SUM");
	}else{
		printAgg("PROD");
	}
}
