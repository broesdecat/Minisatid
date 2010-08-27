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

#include <math.h>
#include <algorithm>

#include "solvers/aggsolver/Agg.hpp"
#include "solvers/aggsolver/AggSets.hpp"
#include "solvers/aggsolver/AggSolver.hpp"

#include "solvers/pcsolver/PCSolver.hpp"

using namespace Aggrs;

AggrReason::AggrReason(pAgg e, const Lit& lit, Expl exp, bool head):
		expr(e),
		l(lit),
		index(e->getSet()->getStack().size()),
		expl(exp),
		head(head) {
}

Agg::Agg(const Bound& bounds, const Weight& bound, const Lit& head, AggrSet* set) :
	    agg(bound, bounds, head), set(set),
	    headindex(-1), headvalue(l_Undef),
	    nomoreprops(false), optimagg(false), headprop(false), headproptime(-1){
	set->addAgg(this);
}

void SumAgg::addToBounds(const Weight& w){
	agg.bound = add(agg.bound, w);
}

/**
 * Returns true if this aggregate can be propagated in the initialization, so it will never change truth value
 * and can be left out of any propagations.
 */
lbool Agg::initialize(){
	rClause confl = nullPtrClause;

	lbool hv = canPropagateHead(getSet()->getCC(), getSet()->getCP());
	if(hv!=l_Undef && !optimagg){
		nomoreprops = true;
		//reportf("No more propagations for %d", gprintVar(var(head)));
	}
	if(hv==l_True){
		confl = getSet()->getSolver()->notifySATsolverOfPropagation(getHead(), new AggrReason(this, getHead(), CPANDCC, true));
	}else if(hv==l_False){
		confl = getSet()->getSolver()->notifySATsolverOfPropagation(~getHead(), new AggrReason(this, ~getHead(), CPANDCC, true));
	}
	if(confl!=nullPtrClause){
		return l_False;
	}

	return nomoreprops?l_True:l_Undef;
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

/**
 * Returns non-owning pointer
 */
rClause Agg::propagateHead(const Lit& p){
	if(nomoreprops || headprop){ return nullPtrClause; }

	bool headtrue = getHead()==p;
	headvalue = headtrue?l_True:l_False;
	headindex = getSet()->getStack().size();
	rClause confl = propagateHead(headtrue);
	return confl;
}

/*****************
 * MAX AGGREGATE *
 *****************/

lbool Agg::canPropagateHead(const Weight& CC, const Weight& CP) const{
	if(nomoreprops || headprop){ return getHeadValue(); }

	if ((isLower() && CC > getLowerBound()) || (isUpper() && CP < getUpperBound())) {
		headproptime = getSet()->getStack().size();
		headprop = true;
		return l_False;
	} else if ((isLower() && CP <= getLowerBound()) || (isUpper() && CC >= getUpperBound())) {
		headproptime = getSet()->getStack().size();
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
/**
 * Returns non-owning pointer
 */
rClause MaxAgg::propagateHead(bool headtrue) {
	if(nomoreprops || headprop){ return nullPtrClause; }

	pSet s = getSet();
	rClause confl = nullPtrClause;
	if (headtrue && isLower()) {
		for(lwlv::const_reverse_iterator i=s->getWL().rbegin(); confl == nullPtrClause && i<s->getWL().rend() && getLowerBound()<(*i).getWeight(); i++){
			//because these propagations are independent of the other set literals, they can also be written as clauses
			confl = s->getSolver()->notifySATsolverOfPropagation(~(*i).getLit(), new AggrReason(this,~(*i).getLit(),HEADONLY));
		}
	}else if(!headtrue && isUpper()){
		for(lwlv::const_reverse_iterator i=s->getWL().rbegin(); confl == nullPtrClause && i<s->getWL().rend() && getUpperBound()<=(*i).getWeight(); i++){
			confl = s->getSolver()->notifySATsolverOfPropagation(~(*i).getLit(), new AggrReason(this,~(*i).getLit(),HEADONLY));
		}
	}
	if(confl==nullPtrClause){
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
/**
 * Returns non-owning pointer
 */
rClause MaxAgg::propagate(bool headtrue) {
	rClause confl = nullPtrClause;

	if(nomoreprops || headprop){ return confl; }

	if((isLower() && headtrue) || (isUpper() && !headtrue)){
		return confl;
	}
	pSet s = getSet();
	lwlv::const_iterator pos = s->getWL().end();
	bool exactlyoneleft = true;
	for(lwlv::const_iterator i=s->getWL().begin(); exactlyoneleft && i<s->getWL().end(); i++){
		if((isUpper() && headtrue && (*i).getWeight()>=getUpperBound()) || (isLower() && !headtrue && (*i).getWeight()>getLowerBound())){
			if((*i).getValue()==l_Undef){
				if(pos!=s->getWL().end()){
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
		//TODO BASEDONCP is not correct enough (ONCPABOVEBOUND)
		confl = s->getSolver()->notifySATsolverOfPropagation((*pos).getLit(), new AggrReason(this, (*pos).getLit(), BASEDONCP));
	}
	return confl;
}

/*****************
 * SUM AGGREGATE *
 *****************/

Weight	SumAgg::add(const Weight& lhs, const Weight& rhs) const{
#ifdef INTWEIGHT
	if(lhs>0 && rhs > 0 && INT_MAX-lhs < rhs){
		return INT_MAX;
	}else if(lhs<0 && rhs<0 && INT_MIN-lhs>rhs){
		return INT_MIN;
	}
#endif
	return lhs+rhs;
}
Weight	SumAgg::remove(const Weight& lhs, const Weight& rhs) const{
	return lhs-rhs;
}
Weight	ProdAgg::add(const Weight& lhs, const Weight& rhs) const{
#ifdef INTWEIGHT
	bool sign = false;
	Weight l = lhs, r = rhs;
	if(l<0){
		l= -l;
		sign = true;
	}
	if(r<0){
		r = -r;
		sign = !sign;
	}
	if(INT_MAX/l < r){
		return sign?INT_MIN:INT_MAX;
	}
#endif
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
/**
 * Returns non-owning pointer
 */
rClause SPAgg::propagateHead(bool headtrue){
	if(nomoreprops || headprop){ return nullPtrClause; }

	return propagate(headtrue);
}

/**
 * Returns non-owning pointer
 */
rClause SPAgg::propagate(bool headtrue){
	if(nomoreprops || headprop){ return nullPtrClause; }

	rClause c = nullPtrClause;
	Weight weightbound(0);
	pSet s = getSet();

	Expl basedon = CPANDCC;

	//determine the lower bound of which weight literals to consider
	if (headtrue) {
		if(isLower()){
			basedon = BASEDONCC;
			weightbound = this->remove(getLowerBound(), s->getCC());
			//+1 because larger and not eq
			if(this->add(weightbound, s->getCC())==getLowerBound()){
				weightbound+=1;
			}
		}else{
			basedon = BASEDONCP;
			weightbound = this->remove(s->getCP(), getUpperBound());
			//+1 because larger and not eq
			if(this->add(weightbound, getUpperBound())==s->getCP()){
				weightbound+=1;
			}
		}
	} else {
		if(isLower()){
			basedon = BASEDONCP;
			weightbound = this->remove(s->getCP(), getLowerBound());
		}else{
			basedon = BASEDONCC;
			weightbound = this->remove(getUpperBound(), s->getCC());
		}
	}

#ifdef INTWEIGHT
	if(weightbound == INT_MAX || weightbound == INT_MIN){
		return c;
	}
#endif

	lwlv::const_iterator pos = lower_bound(s->getWL().begin(), s->getWL().begin(), weightbound);
	if(pos==s->getWL().end()){
		return c;
	}

	//find the index of the literal
	int start = 0;
	lwlv::const_iterator it = s->getWL().begin();
	while(it!=pos){
		it++; start++;
	}

	for (lwlv::const_iterator u = s->getWL().begin()+start; c==nullPtrClause && u < s->getWL().end(); u++) {
		if ((*u).getValue()==l_Undef) {//if already propagated as an aggregate, then those best-values have already been adapted
			if((isLower() && headtrue) || (isUpper() && !headtrue)){
				//assert((headtrue && set->currentbestcertain+set->wlits[u].weight>bound) || (!headtrue && set->currentbestcertain+set->wlits[u].weight>=bound));
				c = s->getSolver()->notifySATsolverOfPropagation(~(*u).getLit(), new AggrReason(this, ~(*u).getLit(), basedon));
			}else{
				//assert((!headtrue && set->currentbestpossible-set->wlits[u].weight<=bound) || (headtrue && set->currentbestpossible-set->wlits[u].weight<bound));
				c = s->getSolver()->notifySATsolverOfPropagation((*u).getLit(), new AggrReason(this, (*u).getLit(), basedon));
			}
		}
	}
	return c;
}

/**
 * Returns non-owning pointer
 */
rClause CardAgg::propagate(bool headtrue){
	if(nomoreprops || headprop){ return nullPtrClause; }

	pSet s = getSet();

	bool makefalse = false;
	bool maketrue = false;
	Expl basedon = BASEDONCC;
	if(headtrue){
		if(isLower() && getLowerBound()==s->getCC()){
			makefalse = true;
			basedon = BASEDONCC;
		}else if(isUpper() && getUpperBound()==s->getCP()){
			maketrue = true;
			basedon = BASEDONCP;
		}
	}else{
		if(isLower() && getLowerBound()+1==s->getCP()){
			maketrue = true;
			basedon = BASEDONCP;
		}else if(isUpper() && getUpperBound()-1==s->getCC()){
			makefalse = true;
			basedon = BASEDONCC;
		}
	}

	rClause c = nullPtrClause;

	if(!makefalse && !maketrue){
		return c;
	}

	for (lwlv::const_iterator u = s->getWL().begin(); c==nullPtrClause && u < s->getWL().end(); u++) {
		if ((*u).getValue()==l_Undef) {//if already propagated as an aggregate, then those best-values have already been adapted
			if(maketrue){
				c = s->getSolver()->notifySATsolverOfPropagation((*u).getLit(), new AggrReason(this, (*u).getLit(), basedon));
			}else{
				c = s->getSolver()->notifySATsolverOfPropagation(~(*u).getLit(), new AggrReason(this, ~(*u).getLit(), basedon));
			}
		}
	}
	return c;
}

/**
 * This method returns a reason clause that is currently false and that explains why the current optimizing
 * sum aggregate is violated. This can serve as a learned clause to backtrack during optimization search.
 */
void SumAgg::getMinimExplan(vec<Lit>& lits){
	pSet s = getSet();
	Weight certainsum = s->getESV();
	Weight possiblesum = s->getBestPossible();

	bool explained = false;
	if((isLower() && certainsum>getLowerBound())
			|| (isUpper() && certainsum>=getUpperBound())
			|| (isLower() && possiblesum <= getLowerBound())
			|| (isUpper() && possiblesum < getUpperBound())){
		explained = true;
	}

	for(lprop::const_iterator i=s->getStack().begin(); !explained && i<s->getStack().end(); i++){
		bool push = false;
		if((*i).getType() == POS){ //means that the literal in the set became true
			certainsum += (*i).getWeight();

			if(isLower()){
				push = true;
				if(getLowerBound() < certainsum){
					explained = true;
				}
			}
		}else if((*i).getType() == NEG){ //the literal in the set became false
			possiblesum -= (*i).getWeight();

			if(isUpper()){
				push = true;
				if(possiblesum < getUpperBound()){
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
 * AGG <= B: v is justified if one literal below/eq the bound is THAT IS NOT THE HEAD
 * 					if so, change the justification to the literal
 * 					otherwise, add all nonfalse, non-justified, relevant, below the bound literals to the queue
 * A <= AGG: v is justified if the negation of all literals below the bound are. The emptyset is always a solution,
 * 			 so no conclusions have to be drawn from the literals above/eq the bound
 * 					if so, change the justification to the negation of all those below the bound literals
 * 					otherwise, add all nonfalse, non-justified, relevant, below the bound literals to the queue
 */
bool MaxAgg::canJustifyHead(vec<Lit>& jstf, vec<Var>& nonjstf, vec<int>& currentjust, bool real) const {
	bool justified = false;
	pSet s = getSet();
	if(isLower()){
		for(lwlv::const_reverse_iterator i=s->getWL().rbegin(); i<s->getWL().rend() && (*i).getWeight()>getLowerBound(); i++) {
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
		for(lwlv::const_reverse_iterator i=s->getWL().rbegin(); i<s->getWL().rend() && (*i).getWeight()>=getUpperBound(); i++) {
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
 * AGG <= B: add a number of justified literals such that they guarantee the bestpossible value is below the bound
 * A <= AGG: need a justification of which the sum exceed/eq the bound
 */
bool SPAgg::canJustifyHead(vec<Lit>& jstf, vec<Var>& nonjstf, vec<int>& currentjust, bool real) const {
	bool justified = false;
	pSet s = getSet();

	if(isLower()){
		Weight bestpossible = s->getBestPossible();
		for (lwlv::const_iterator i = s->getWL().begin(); !justified && i < s->getWL().end(); ++i) {
			if(s->oppositeIsJustified(*i, currentjust, real)){
				jstf.push(~(*i).getLit());
				bestpossible = this->remove(bestpossible, (*i).getWeight());
				if (bestpossible <= getLowerBound()){
					justified = true;
				}
			}else if(real ||currentjust[var((*i).getLit())]!=0){
				nonjstf.push(var((*i).getLit()));
			}
		}
	}else{
		Weight bestcertain = s->getESV();
		for (lwlv::const_iterator i = s->getWL().begin(); !justified && i < s->getWL().end(); ++i) {
			if(s->isJustified(*i, currentjust, real)){
				jstf.push((*i).getLit());
				bestcertain = this->add(bestcertain, (*i).getWeight());
				if (bestcertain >= getUpperBound()){
					justified = true;
				}
			}else if(real ||currentjust[var((*i).getLit())]!=0){
				nonjstf.push(var((*i).getLit()));
			}
		}
	}

	if(s->getSolver()->getPCSolver()->modes().verbosity >=4){
		reportf("Justification checked for ");
		printAggrExpr(this);

		if(justified){
			reportf("justification found: ");
			for(int i=0; i<jstf.size(); i++){
				gprintLit(jstf[i]); reportf(" ");
			}
			reportf("\n");
		}else{
			reportf("no justification found.\n");
		}
	}

	return justified;
}

/*bool SPAgg::canJustifyHead(vec<Lit>& jstf, vec<Var>& nonjstf, vec<int>& currentjust, bool real) const {
	//OTHER IMPLEMENTATION (probably buggy)
	pSet s = getSet();

	Weight current = 0;
	if(isLower()){
		current = s->getBestPossible();
	}else{
		current = s->getEmptySetValue();
	}

	bool justified = false;
	if(aggValueImpliesHead(current)){
		justified = true;
	}

	for (lwlv::const_iterator i = s->getWLBegin(); !justified && i < s->getWLEnd(); ++i) {
		if(isMonotone(*i) && s->isJustified(*i, currentjust, real)){
			if(isLower()){
				jstf.push(~(*i).getLit());
				current = this->remove(current, (*i).getWeight());
			}else{
				//if(s->isJustified(*i, currentjust, real)){
				jstf.push((*i).getLit());
				current = this->add(current, (*i).getWeight());
			}

			if (aggValueImpliesHead(current)){
				justified = true;
			}
		}else if(real ||currentjust[var((*i).getLit())]!=0){
			nonjstf.push(var((*i).getLit()));
		}
	}

	if (!justified) {
		jstf.clear();
	}

	if(s->getSolver()->getPCSolver()->modes().verbosity >=4){
		reportf("Justification checked for ");
		printAggrExpr(this);

		if(justified){
			reportf("justification found: ");
			for(int i=0; i<jstf.size(); i++){
				gprintLit(jstf[i]); reportf(" ");
			}
			reportf("\n");
		}else{
			reportf("no justification found.\n");
		}
	}

	return justified;
}*/

bool MaxAgg::isMonotone(const WLV& l) const{
	return (isLower() && l.getWeight()<=getLowerBound()) || (isUpper() && l.getWeight()>=getUpperBound());
}

bool SumAgg::isMonotone(const WLV& l) const{
	return (isLower() && l.getWeight()<0) || (isUpper() && l.getWeight()>0);
}

bool ProdAgg::isMonotone(const WLV& l) const{
	assert(l.getWeight()==0 || l.getWeight()>=1);
	return isUpper();
}

///////
// DEBUG
///////

void Aggrs::printAggrExpr(const Agg* ae){
	gprintLit(ae->getHead(), ae->getHeadValue());
	pSet set = ae->getSet();
	if(ae->isLower()){
		reportf(" <- ");
	}else{
		reportf(" <- %s <= ", printWeight(ae->getUpperBound()).c_str());
	}
	printAggrSet(set, false);
	if(ae->isLower()){
		reportf(" <= %s. Known values: bestcertain=%s, bestpossible=%s\n", printWeight(ae->getLowerBound()).c_str(), printWeight(set->getCC()).c_str(), printWeight(set->getCP()).c_str());
	}else{
		reportf(". Known values: bestcertain=%s, bestpossible=%s\n", printWeight(set->getCC()).c_str(), printWeight(set->getCP()).c_str());
	}
}
