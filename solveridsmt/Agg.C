#include "Agg.h"
#include "AggSolver.h"

lbool Agg::value(Lit p){
	return AggSolver::aggsolver->value(p);
}

void Agg::backtrack(WLit l, bool wasinset) {
	if (wasinset) {
		truecount--;
		if (truecount == 0) {
			currentworst = emptysetValue;
		} else {
			if (l.weight == currentworst) {
				currentworst = getCurrentBestCertain();
			}
		}
	} else {
		if (l.weight == currentbest) {
			currentbest = getCurrentBestPossible();
		}
	}
}

void Agg::initialize() {
	currentbest = getCurrentBestPossible(true);
	currentworst = emptysetValue;
}

lbool Agg::updateAndCheckPropagate(WLit l, bool addtoset) {
	//update values
	if (addtoset) {
		truecount++;
		if (l.weight == currentworst) {
			currentworst = getCurrentBestCertain();
		}
	} else {
		if (l.weight == currentbest) {
			currentbest = getCurrentBestPossible();
		}
	}

	//check if propagation possible
	if ((lower && currentworst > bound) || (!lower && currentbest < bound)) {
		return l_False;
	} else if ((lower && currentbest <= bound)	|| (!lower && currentworst >= bound)) {
		return l_True;
	} else {
		return l_Undef;
	}
}



int MinAgg::getCurrentBestPossible(bool alltimebest){
	int min = emptysetValue;
	for (int j = 0; j < set->wlitset.size(); j++) {
		if(alltimebest || (value(set->wlitset[j].lit)!=l_False && min > set->wlitset[j].weight)){
			min = set->wlitset[j].weight;
		}
	}
	return min;
}

int MinAgg::getCurrentBestCertain() {
	int min = emptysetValue;
	for (int j = 0; j < set->wlitset.size(); j++) {
		if(value(set->wlitset[j].lit)==l_True && min > set->wlitset[j].weight){
			min = set->wlitset[j].weight;
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
		if (l.weight == currentworst) {
			currentworst = getCurrentBestCertain();
		}
	} else {
		if (l.weight == currentbest) {
			currentbest = getCurrentBestPossible();
		}
	}

	//check if propagation possible
	if ((lower && currentbest > bound) || (!lower && currentworst < bound)) {
		return l_False;
	} else if ((lower && currentworst <= bound)
			|| (!lower && currentbest >= bound)) {
		return l_True;
	} else {
		return l_Undef;
	}
}

//TODO de literals in de set zijn geordend naar stijgende weight, zodat gericht kan worden gezocht
//FIXME GEBRUIK deze optimalisatie

/**
 * If the head is true && A <= AGG, make all literals false that would make the minimum lower than the bound
 * If the head is false && AGG <= B, make all literals false that would make the minimum lower than the bound
 */
Clause* MinAgg::propagate(bool headtrue) {
	Clause* confl = NULL;
	if ((headtrue && !lower) ||	(!headtrue && lower)) {
		for(int i=0; confl==NULL && i<set->wlitset.size(); i++){
			if(set->wlitset[i].weight<=bound){
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

int MaxAgg::getCurrentBestPossible(bool alltimebest){
	int max = emptysetValue;
	for (int j = 0; j < set->wlitset.size(); j++) {
		if(alltimebest || value(set->wlitset[j].lit)!=l_False && max < set->wlitset[j].weight){
			max = set->wlitset[j].weight;
		}
	}
	return max;
}

int MaxAgg::getCurrentBestCertain() {
	int max = emptysetValue;
	for (int j = 0; j < set->wlitset.size(); j++) {
		if(value(set->wlitset[j].lit)==l_True && max < set->wlitset[j].weight){
			max = set->wlitset[j].weight;
		}
	}
	return max;
}

Clause* MaxAgg::propagate(bool headtrue) {
	/*if (value(ae.c) == l_True) {
	 for (int u = as.max; confl == NULL && u >= 0 && as.set[u].weight> ae.max; --u)
	 confl = aggrEnqueue(~as.set[u].lit, new AggrReason(&ae, &as,NEG));
	 } else if (value(ae.c) == l_False) {
	 if (as.max >= 0 && as.set[as.max].weight <= ae.max)
	 for (int u = as.max; confl == NULL && u >= 0
	 && as.set[u].weight >= ae.min; --u)
	 confl = aggrEnqueue(~as.set[u].lit, new AggrReason(&ae,	&as, NEG));
	 }*/
	return NULL;
}

/*****************
 * SUM AGGREGATE *
 *****************/

SumAgg::~SumAgg() {
}

int SumAgg::getCurrentBestPossible(bool alltimebest){
	int max = emptysetValue;
	for (int j = 0; j < set->wlitset.size(); j++) {
		if(alltimebest || value(set->wlitset[j].lit)!=l_False){
			max += set->wlitset[j].weight;
		}
	}
	return max;
}

int SumAgg::getCurrentBestCertain() {
	int max = emptysetValue;
	for (int j = 0; j < set->wlitset.size(); j++) {
		if(value(set->wlitset[j].lit)==l_True){
			max += set->wlitset[j].weight;
		}
	}
	return max;
}

/**
 * If head is true, and making a literal true would increase the minimum above the bound (and gEQ)
 * 					or  making a literal false would decrease the maximum below the bound (and lEQ)
 * 		then enqueue the negative (resp. positive) literal
 *
 * If head is false, find the minimum weight of unknown literals
 * 		if making the literal true, would make the aggregate true, then make it and all higher ones false
 * 		and vice versa
 */
Clause* SumAgg::propagate(bool headtrue) {
	/*if (headtrue) {
	 for (int u = 0; u < set->wlitset.size(); u++) {
	 if (value(set->wlitset[u].lit) == l_Undef) {// no conflict possible
	 if (lower && currentworst + set->wlitset[u].weight > bound){
	 aggrEnqueue(~set->wlitset[u].lit, new AggrReason(&ae, NEG));
	 }else if (!lower && currentbest - set->wlitset[u].weight < bound)
	 aggrEnqueue(set->wlitset[u].lit, new AggrReason(&ae, POS));
	 }
	 }
	 } else {
	 if (as.min >= ae.min || as.max <= ae.max) {// no conflicts possible
	 int minw = 2147483647;
	 for (int u = 0; u < as.set.size(); u++)
	 if (value(as.set[u].lit) == l_Undef && as.set[u].weight	< minw)
	 minw = as.set[u].weight;
	 bool maketrue = minw != 2147483647 && as.min >= ae.min
	 && as.max - minw <= ae.max;
	 bool makefalse = minw != 2147483647 && as.max <= ae.max
	 && as.min + minw >= ae.min;
	 if (maketrue)
	 for (int u = 0; u < as.set.size(); u++)
	 if (value(as.set[u].lit) == l_Undef)
	 aggrEnqueue(as.set[u].lit, new AggrReason(&ae, &as,	POS));
	 if (makefalse)
	 for (int u = 0; u < as.set.size(); u++)
	 if (value(as.set[u].lit) == l_Undef)
	 aggrEnqueue(~as.set[u].lit, new AggrReason(&ae,	&as, NEG));
	 }
	 }*/
	return NULL;
}

/*********************
 * PRODUCT AGGREGATE *
 *********************/

ProdAgg::~ProdAgg() {
}

int ProdAgg::getCurrentBestPossible(bool alltimebest){
	int max = emptysetValue;
	for (int j = 0; j < set->wlitset.size(); j++) {
		if(alltimebest || value(set->wlitset[j].lit)!=l_False){
			max *= set->wlitset[j].weight;
		}
	}
	return max;
}

int ProdAgg::getCurrentBestCertain() {
	int max = emptysetValue;
	for (int j = 0; j < set->wlitset.size(); j++) {
		if(value(set->wlitset[j].lit)==l_True){
			max *= set->wlitset[j].weight;
		}
	}
	return max;
}

Clause* ProdAgg::propagate(bool headtrue) {
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
