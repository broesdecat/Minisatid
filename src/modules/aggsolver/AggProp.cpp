#include "modules/aggsolver/AggProp.hpp"
#include "modules/aggsolver/AggPrint.hpp"
#include "modules/aggsolver/AggUtils.hpp"
#include "modules/AggSolver.hpp"
#include "theorysolvers/PCSolver.hpp"

#include "modules/aggsolver/FullyWatched.hpp"
#include "modules/aggsolver/PartiallyWatched.hpp"

#include "utils/Print.hpp"

#include <assert.h>

using namespace std;
#ifndef __GXX_EXPERIMENTAL_CXX0X__
using namespace std::tr1;
#endif
using namespace MinisatID;
using namespace MinisatID::Print;
using namespace Aggrs;

Weight	Agg::getCertainBound() const {
	return bound.bound-getSet()->getKnownBound();
}

paggprop AggProp::max = paggprop (new MaxProp());
paggprop AggProp::sum = paggprop (new SumProp());
paggprop AggProp::card = paggprop (new CardProp());
paggprop AggProp::prod = paggprop (new ProdProp());

bool MaxProp::isMonotone(const Agg& agg, const Weight& w) const {
	const Weight& w2 = agg.getCertainBound();
	return (agg.hasUB() && w <= w) || (!agg.hasUB());
}

bool SumProp::isMonotone(const Agg& agg, const Weight& w) const {
	return (agg.hasUB() && w < 0) || (!agg.hasUB() && w > 0);
}

bool ProdProp::isMonotone(const Agg& agg, const Weight& w) const {
	assert(w == 0 || w >= 1);
	return !agg.hasUB();
}

Weight SumProp::add(const Weight& lhs, const Weight& rhs) const {
#ifdef NOARBITPREC
	if (lhs > 0 && rhs > 0 && posInfinity() - lhs < rhs) {
		return posInfinity();
	} else if (lhs < 0 && rhs < 0 && negInfinity() - lhs > rhs) {
		return negInfinity();
	}
#endif
	return lhs + rhs;
}

Weight SumProp::remove(const Weight& lhs, const Weight& rhs) const {
	return lhs - rhs;
}

Weight SumProp::getMinPossible(const TypedSet& set) const{
	Weight min = getESV();
	for (vwl::const_iterator j = set.getWL().begin(); j < set.getWL().end(); j++) {
		if((*j).getWeight() < 0){
			min = this->add(min, (*j).getWeight());
		}
	}
	return min;
}

Weight SumProp::getMaxPossible(const TypedSet& set) const {
	Weight max = getESV();
	for (vwl::const_iterator j = set.getWL().begin(); j < set.getWL().end(); j++) {
		if((*j).getWeight() > 0){
			max = this->add(max, (*j).getWeight());
		}
	}
	return max;
}

Weight SumProp::getCombinedWeight(const Weight& one, const Weight& two) const {
	return this->add(one, two);
}

WL SumProp::handleOccurenceOfBothSigns(const WL& one, const WL& two, TypedSet* set) const {
	if (one.getWeight() < two.getWeight()) {
		set->setKnownBound(set->getKnownBound() + one.getWeight());
		return WL(two.getLit(), this->remove(two.getWeight(), one.getWeight()));
	} else {
		set->setKnownBound(set->getKnownBound() + two.getWeight());
		return WL(one.getLit(), this->remove(one.getWeight(), two.getWeight()));
	}
}

///////
// MAX Prop
///////

Weight MaxProp::getMinPossible(const TypedSet&) const{
	return getESV();
}

Weight MaxProp::getMaxPossible(const TypedSet& set) const {
	Weight max = getESV();
	for(vwl::const_iterator j = set.getWL().begin(); j<set.getWL().end(); j++){
		max = this->add(max, (*j).getWeight());
	}
	return max;
}

Weight MaxProp::getCombinedWeight(const Weight& first, const Weight& second) const {
	return first > second ? first : second;
}

WL MaxProp::handleOccurenceOfBothSigns(const WL& one, const WL& two, TypedSet* set) const {
	if (one.getWeight() > two.getWeight()) {
		if (set->getKnownBound() < two.getWeight()) {
			set->setKnownBound(two.getWeight());
		}
		return one;
	} else {
		if (set->getKnownBound() < one.getWeight()) {
			set->setKnownBound(one.getWeight());
		}
		return two;
	}
}

///////
// PROD Prop
///////

//TODO INVARIANT: only positive weights in prodagg
Weight ProdProp::getMinPossible(const TypedSet&) const{
	return getESV();
}

Weight ProdProp::getMaxPossible(const TypedSet& set) const {
	Weight max = getESV();
	for(vwl::const_iterator j = set.getWL().begin(); j<set.getWL().end(); j++){
		if((*j).getWeight() > 0){
			max = this->add(max, (*j).getWeight());
		}
	}
	return max;
}

Weight ProdProp::add(const Weight& lhs, const Weight& rhs) const {
	assert(lhs!=0 && rhs!=0);
#ifdef NOARBITPREC
	bool sign = false;
	Weight l = lhs, r = rhs;
	if(l<0){
		l = -l;
		sign = true;
	}
	if(r<0){
		r = -r;
		sign = !sign;
	}
	if(posInfinity()/l < r){
		return sign ? negInfinity() : posInfinity();
	}
#endif
	return lhs * rhs;
}

Weight ProdProp::remove(const Weight& lhs, const Weight& rhs) const {
	Weight w = 0;
	assert(rhs!=0); //FIXME should prevent this from happening
	if (rhs != 0) {
		w = lhs / rhs;
		if (w == 1 && lhs > rhs) {
			w = 2;
		}
	}

	return w;
}

Weight ProdProp::getCombinedWeight(const Weight& one, const Weight& two) const {
	return this->add(one, two);
}

WL ProdProp::handleOccurenceOfBothSigns(const WL& one, const WL& two, TypedSet* set) const {
	//NOTE: om dit toe te laten, ofwel bij elke operatie op en literal al zijn voorkomens overlopen
	//ofwel aggregaten voor doubles ondersteunen (het eerste is eigenlijk de beste oplossing)
	//Mogelijke eenvoudige implementatie: weigts bijhouden als doubles (en al de rest als ints)
	report("Product aggregates in which both the literal and its negation occur "
			"are currently not supported. Replace ");
	Print::print(one.getLit());
	report("or ");
	Print::print(two.getLit());
	report("by a tseitin.\n");
	throw idpexception("Atoms in product aggregates have to be unique.\n");
}

//AGGREGATES

bool Aggrs::isSatisfied(const Agg& agg, const Weight& min, const Weight& max){
	if(agg.hasUB()){
		return max<=agg.getCertainBound();
	}else{ //LB
		return min>=agg.getCertainBound();
	}
}

bool Aggrs::isSatisfied(const Agg& agg, const minmaxBounds& bounds){
	if(agg.hasUB()){
		return bounds.max<=agg.getCertainBound();
	}else{ //LB
		return bounds.min>=agg.getCertainBound();
	}
}

bool Aggrs::isFalsified(const Agg& agg, const Weight& min, const Weight& max){
	if(agg.hasUB()){
		return min>agg.getCertainBound();
	}else{ //LB
		return max<agg.getCertainBound();
	}
}

bool Aggrs::isFalsified(const Agg& agg, const minmaxBounds& bounds){
	if(agg.hasUB()){
		return bounds.min>agg.getCertainBound();
	}else{ //LB
		return bounds.max<agg.getCertainBound();
	}
}

/**
 * IMPORTANT: not usable for types without remove!
 * if addtoset: weight should be considered as the weight of a literal being added to the set (from unknown)
 * 		if weight is pos: min will increase, so add to min
 * 		if weight is neg: max will decrease, so add to max
 * if !addtoset: consider weight as weight of the literal being removed from the set (from unknown)
 * 		if weight is pos: max will decrease, so remove from max
 * 		if weight is neg: min will increase, so remove from min
 */
void Aggrs::addValue(const AggProp& type, const Weight& weight, bool addtoset, minmaxBounds& bounds){
	addValue(type, weight, addtoset, bounds.min, bounds.max);
}
void Aggrs::addValue(const AggProp& type, const Weight& weight, bool addtoset, Weight& min, Weight& max){
	bool pos = weight>=0;
	if(pos && addtoset){
		min = type.add(min, weight);
	}else if(pos && !addtoset){
		max = type.remove(max, weight);
	}else if(!pos && addtoset){
		max = type.add(max, weight);
	}else{ //!pos && !addtoset
		min = type.remove(min, weight);
	}
}

void Aggrs::removeValue(const AggProp& type, const Weight& weight, bool wasinset, minmaxBounds& bounds) {
	removeValue(type, weight, wasinset, bounds.min, bounds.max);
}

void Aggrs::removeValue(const AggProp& type, const Weight& weight, bool wasinset, Weight& min, Weight& max) {
	bool pos = weight>=0;
	if(pos && wasinset){
		min = type.remove(min, weight);
	}else if(pos && !wasinset){
		max = type.add(max, weight);
	}else if(!pos && wasinset){
		max = type.remove(max, weight);
	}else{ //!pos && !wasinset
		min = type.add(min, weight);
	}
}

///////
// TypedSet
///////

Propagator*	MaxProp::createPropagator(TypedSet* set, bool pw) const{
	//FIXME watched?
	return new MaxFWAgg(set);
}

Propagator*	SumProp::createPropagator(TypedSet* set, bool pw) const{
	//Extremely ugly!
	if(pw && !set->getAgg()[0]->isDefined() && set->getAgg()[0]->getSem()==IMPLICATION){
		if(getType()==CARD){
			return new CardGenPWAgg(set);
		}else{
			return new SumGenPWAgg(set);
		}
	}
	return new SumFWAgg(set);
}

Propagator*	ProdProp::createPropagator(TypedSet* set, bool pw) const{
	if(pw && !set->getAgg()[0]->isDefined() && set->getAgg()[0]->getSem()==IMPLICATION){
		return new GenPWAgg(set);
	}
	return new ProdFWAgg(set);
}

void TypedSet::addAgg(Agg* aggr){
	assert(aggr!=NULL);
	aggregates.push_back(aggr);
	aggr->setTypedSet(this);
	aggr->setIndex(aggregates.size()-1);
}

//FIXME should add check that aggregate is indeed still referring to that set
void TypedSet::replaceAgg(const vpagg& repl){
	for(vpagg::const_iterator i=aggregates.begin(); i<aggregates.end(); i++){
		(*i)->setTypedSet(NULL);
		(*i)->setIndex(-1);
	}
	aggregates.clear();
	for(vpagg::const_iterator i=repl.begin(); i<repl.end(); i++){
		addAgg(*i);
	}
}

void TypedSet::replaceAgg(const vpagg& repl, const vpagg& del){
	replaceAgg(repl);
	for(vpagg::const_iterator i=del.begin(); i<del.end(); i++){
		delete *i;
	}
}

/*
 * Initialize the datastructures. If it's neither sat nor unsat and it is defined, notify the pcsolver of this
 */
void TypedSet::initialize(bool& unsat, bool& sat, vps& sets) {
	for(vector<AggTransform*>::iterator i=transformations.begin(); !sat && !unsat && i<transformations.end(); i++) {
		AggTransform* transfo = *i;
		transformations.erase(i); i--;
		transfo->transform(getSolver(), this, sets, unsat, sat);
	}

	if(sat || unsat){ return; }

	setProp(getType().createPropagator(this, this->getSolver()->getPCSolver()->modes().watchedagg));
	prop->initialize(unsat, sat);

	if(sat || unsat){ return; }

	for (vpagg::const_iterator i = getAgg().begin(); i < getAgg().end(); i++) {
		if ((*i)->isDefined()) {
			getSolver()->notifyDefinedHead(var((*i)->getHead()));
		}
	}
}

void TypedSet::getExplanation(vec<Lit>& lits, const AggReason& ar) const {
	getProp()->getExplanation(lits, ar);

	if(getSolver()->verbosity()>=3){
		report("Explanation for deriving "); Print::print(ar.getPropLit());
		report(" in expression ");
		print(getSolver()->verbosity(), ar.getAgg(), false);
		report(" is ");
		for(int i=0; i<lits.size(); i++){
			report(" "); Print::print(lits[i]);
		}
		report("\n");
	}
}

Propagator::Propagator(TypedSet* set):set(set), aggsolver(set->getSolver()){

}

// Final initialization call!
void Propagator::initialize(bool& unsat, bool& sat) {
	for (vpagg::const_iterator i = getSet().getAgg().begin(); i < getSet().getAgg().end(); i++) {
		if((*i)->getSem()==IMPLICATION){
			getSolver()->setHeadWatch(~(*i)->getHead(), (*i));
		}else{
			getSolver()->setHeadWatch((*i)->getHead(), (*i));
			getSolver()->setHeadWatch(~(*i)->getHead(), (*i));
		}
	}
}

lbool Propagator::value(const Lit& l) const {
	return getSolver()->value(l);
}

/************************
 * RECURSIVE AGGREGATES *
 ************************/

bool MaxProp::canJustifyHead(const Agg& agg, vec<Lit>& jstf, vec<Var>& nonjstf, VarToJustif& currentjust, bool real) const {
	TypedSet* set = agg.getSet();
	bool justified = true;
	const vwl& wl = set->getWL();

	if (justified && agg.hasUB()) {
		justified = false;
		for (vwl::const_reverse_iterator i = wl.rbegin(); i < wl.rend() && (*i).getWeight() > agg.getCertainBound(); i++) {
			if (oppositeIsJustified(*i, currentjust, real, set->getSolver())) {
				jstf.push(~(*i).getLit()); //push negative literal, because it should become false
			} else if (real || currentjust[var((*i).getLit())] != 0) {
				nonjstf.push(var((*i).getLit()));
			}
		}
		if (nonjstf.size() == 0) {
			justified = true;
		}
	}

	if(justified && agg.hasLB()){
		justified = false;
		for (vwl::const_reverse_iterator i = wl.rbegin(); i < wl.rend() && (*i).getWeight() >= agg.getCertainBound(); i++) {
			if (isJustified(*i, currentjust, real, set->getSolver())) {
				jstf.push((*i).getLit());
				justified = true;
			} else if (real || currentjust[var((*i).getLit())] != 0) {
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
 * AGG <= B: v is justified if one literal below/eq the bound is THAT IS NOT THE HEAD
 * 					if so, change the justification to the literal
 * 					otherwise, add all nonfalse, non-justified, relevant, below the bound literals to the queue
 * A <= AGG: v is justified if the negation of all literals below the bound are. The emptyset is always a solution,
 * 			 so no conclusions have to be drawn from the literals above/eq the bound
 * 					if so, change the justification to the negation of all those below the bound literals
 * 					otherwise, add all nonfalse, non-justified, relevant, below the bound literals to the queue
 */
bool SPProp::canJustifyHead(const Agg& agg, vec<Lit>& jstf, vec<Var>& nonjstf, VarToJustif& currentjust, bool real) const {
	TypedSet* set = agg.getSet();
	const AggProp& type = agg.getSet()->getType();
	bool justified = true;
	const vwl& wl = set->getWL();

	if (justified && agg.hasUB()) {
		justified = false;
		Weight bestpossible = type.getMaxPossible(*set);
		for (vwl::const_iterator i = wl.begin(); !justified && i < wl.end(); ++i) {
			if (oppositeIsJustified(*i, currentjust, real, set->getSolver())) {
				jstf.push(~(*i).getLit());
				bestpossible = type.remove(bestpossible, (*i).getWeight());
				if (bestpossible <= agg.getCertainBound()) {
					justified = true;
				}
			} else if (real || currentjust[var((*i).getLit())] != 0) {
				nonjstf.push(var((*i).getLit()));
			}
		}
	}
	if(justified && agg.hasLB()){
		justified = false;
		Weight bestcertain = set->getType().getMinPossible(*set);
		for (vwl::const_iterator i = wl.begin(); !justified && i < wl.end(); ++i) {
			if (isJustified(*i, currentjust, real, set->getSolver())) {
				jstf.push((*i).getLit());
				bestcertain = type.add(bestcertain, (*i).getWeight());
				if (bestcertain >= agg.getCertainBound()) {
					justified = true;
				}
			} else if (real || currentjust[var((*i).getLit())] != 0) {
				nonjstf.push(var((*i).getLit()));
			}
		}
	}

	if (!justified) {
		jstf.clear();
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
 print(jstf[i]); reportf(" ");
 }
 reportf("\n");
 }else{
 reportf("no justification found.\n");
 }
 }

 return justified;
 }*/
