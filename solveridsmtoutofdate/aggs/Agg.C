#include <math.h>
#include <algorithm>

#include "Agg.h"
#include "AggSets.h"
#include "AggSolver.h"

using namespace Aggrs;

AggrReason::AggrReason(pAgg e, Expl exp, bool head): expr(e), index(0), expl(exp) {
	index = e->getSet()->getStackSize();
	if(head==true){
		index = -index;
	}
}

void Agg::addAggToSet(){
	set->addAgg(this);
}

/**
 * Returns true if this aggregate can be propagated in the initialization, so it will never change truth value
 * and can be left out of any propagations.
 */
bool Agg::initialize(){
	Clause* confl = NULL;

	lbool hv = canPropagateHead(getSet()->getCC(), getSet()->getCP());
	if(hv!=l_Undef && !optimagg){
		nomoreprops = true;
		//reportf("No more propagations for %d", gprintVar(var(head)));
	}
	if(hv==l_True){
		confl = getSet()->getSolver()->notifySATsolverOfPropagation(head, new AggrReason(this, CPANDCC, true));
	}else if(hv==l_False){
		confl = getSet()->getSolver()->notifySATsolverOfPropagation(~head, new AggrReason(this, CPANDCC, true));
	}
	if(confl!=NULL){
		throw UNSAT();
	}
	return nomoreprops;
}

void Agg::backtrack(int stacksize){
	if(headprop && headproptime>stacksize){
		headprop = false;
	}
}

void Agg::backtrackHead(){
	if(nomoreprops){ return; }

	headvalue = l_Undef;
	headindex = -1;
}

Clause* Agg::propagateHead(const Lit& p){
	if(nomoreprops || headprop){ return NULL; }

	bool headtrue = head==p;
	headvalue = headtrue?l_True:l_False;
	headindex = set->getStackSize();
	Clause* confl = propagateHead(headtrue);
	return confl;
}

/*****************
 * MAX AGGREGATE *
 *****************/

lbool Agg::canPropagateHead(const Weight& CC, const Weight& CP) const{
	if(nomoreprops || headprop){ return headvalue; }

	if ((lower && CC > bound) || (!lower && CP < bound)) {
		headproptime = getSet()->getStackSize();
		headprop = true;
		return l_False;
	} else if ((lower && CP <= bound) || (!lower && CC >= bound)) {
		headproptime = getSet()->getStackSize();
		headprop = true;
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
	if(nomoreprops || headprop){ return NULL; }

	pSet s = set;
	Clause* confl = NULL;
	if (headtrue && lower) {
		lwlv::const_reverse_iterator i=s->getWLRBegin();
		while( confl == NULL && i<s->getWLREnd() && bound<(*i).getWeight()){
			//because these propagations are independent of the other set literals, they can also be written as clauses
			confl = s->getSolver()->notifySATsolverOfPropagation(~(*i).getLit(), new AggrReason(this,HEADONLY));
			i++;
		}
	}else if(!headtrue && !lower){
		lwlv::const_reverse_iterator i=s->getWLRBegin();
		while( confl == NULL && i<s->getWLREnd() && bound<=(*i).getWeight()){
			confl = s->getSolver()->notifySATsolverOfPropagation(~(*i).getLit(), new AggrReason(this,HEADONLY));
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

	if(nomoreprops || headprop){ return confl; }

	if((lower && headtrue) || (!lower && !headtrue)){
		return confl;
	}
	pSet s = set;
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
		//FIXME BASEDONCP is not correct enough (ONCPABOVEBOUND)
		confl = s->getSolver()->notifySATsolverOfPropagation((*pos).getLit(), new AggrReason(this, BASEDONCP));
	}
	return confl;
}

/*****************
 * SUM AGGREGATE *
 *****************/

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
	Weight w = 0;
	if(rhs!=0){
		w = lhs/rhs;
		if(w==1 && lhs>rhs){
			w=2;
		}
	}

	return w;
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
	if(nomoreprops || headprop){ return NULL; }

	return propagate(headtrue);
}

Clause* SPAgg::propagate(bool headtrue){
	if(nomoreprops || headprop){ return NULL; }

	Clause* c = NULL;
	Weight weightbound(0);
	pSet s = set;

	Expl basedon = CPANDCC;

	//determine the lower bound of which weight literals to consider
	if (headtrue) {
		if(lower){
			basedon = BASEDONCC;
			weightbound = this->remove(bound, s->getCC());
			//+1 because larger and not eq
			if(this->add(weightbound, s->getCC())==bound){
				weightbound+=1;
			}
		}else{
			basedon = BASEDONCP;
			weightbound = this->remove(s->getCP(), bound);
			//+1 because larger and not eq
			if(this->add(weightbound, bound)==s->getCP()){
				weightbound+=1;
			}
		}
	} else {
		if(lower){
			basedon = BASEDONCP;
			weightbound = this->remove(s->getCP(), bound);
		}else{
			basedon = BASEDONCC;
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
				c = s->getSolver()->notifySATsolverOfPropagation(~(*u).getLit(), new AggrReason(this, basedon));
			}else{
				//assert((!headtrue && set->currentbestpossible-set->wlits[u].weight<=bound) || (headtrue && set->currentbestpossible-set->wlits[u].weight<bound));
				c = s->getSolver()->notifySATsolverOfPropagation((*u).getLit(), new AggrReason(this, basedon));
			}
		}
	}
	return c;
}

void Agg::getExplanation(vec<Lit>& lits, AggrReason& ar) const{
	assert(ar.getAgg() == this);

	if(!ar.isHeadReason() && ar.getIndex() >= headindex){
		//the head literal is saved as it occurred in the theory, so adapt for its current truth value!
		lits.push(headvalue==l_True?~head:head);
	}

	int counter = 0;
	pSet s = set;

	assert(ar.isHeadReason() || ar.getIndex()<=s->getStackSize());

//	This is correct, but not minimal enough. We expect to be able to do better
//	for(lprop::const_iterator i=s->getStackBegin(); counter<ar.getIndex() && i<s->getStackEnd(); i++,counter++){
//		lits.push(~(*i).getLit());
//	}

	if(ar.getExpl()!=HEADONLY){
		for(lprop::const_iterator i=s->getStackBegin(); counter<ar.getIndex() && i<s->getStackEnd(); i++,counter++){
			switch(ar.getExpl()){
			case BASEDONCC:
				if((*i).getType()==POS){
					lits.push(~(*i).getLit());
				}
				break;
			case BASEDONCP:
				if((*i).getType()==NEG){
					lits.push(~(*i).getLit());
				}
				break;
			case CPANDCC:
				lits.push(~(*i).getLit());
				break;
			}
		}
	}





	if(verbosity>=5){
		reportf("Aggregate explanation for ");
		if(ar.isHeadReason()){
			gprintLit(getHead());
		}else{
			gprintLit((*(s->getStackBegin()+ar.getIndex())).getLit());
		}

		reportf(" is");
		for(int i=0; i<lits.size(); i++){
			reportf(" ");
			gprintLit(lits[i]);
		}
		reportf("\n");
	}
}

/**
 * This method returns a reason clause that is currently false and that explains why the current optimizing
 * sum aggregate is violated. This can serve as a learned clause to backtrack during optimization search.
 */
void SumAgg::getMinimExplan(vec<Lit>& lits){
	pSet s = set;
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
	pSet s = set;
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
	pSet s = set;
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

	pSet pset = set;
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
	pSet s = set;

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

//=========== DEBUG =================

void Aggrs::printAggrSet(pSet set, bool endl){
	reportf("%s{", set->getName().c_str());
	for (lwlv::const_iterator i=set->getWLBegin(); i<set->getWLEnd(); ++i) {
		reportf(" "); gprintLit((*i).getLit(), (*i).getValue()); reportf("(%s)",printWeight((*i).getWeight()).c_str());
	}
	if(endl){
		reportf(" }\n");
	}else{
		reportf(" }");
	}
}

void Aggrs::printAggrExpr(pAgg ae){
	gprintLit(ae->getHead(), ae->getHeadValue());
	pSet set = ae->getSet();
	if(ae->isLower()){
		reportf(" <- ");
	}else{
		reportf(" <- %s <= ", printWeight(ae->getBound()).c_str());
	}
	printAggrSet(set, false);
	if(ae->isLower()){
		reportf(" <= %s. Known values: bestcertain=%s, bestpossible=%s\n", printWeight(ae->getBound()).c_str(), printWeight(set->getCC()).c_str(), printWeight(set->getCP()).c_str());
	}else{
		reportf(". Known values: bestcertain=%s, bestpossible=%s\n", printWeight(set->getCC()).c_str(), printWeight(set->getCP()).c_str());
	}
}
