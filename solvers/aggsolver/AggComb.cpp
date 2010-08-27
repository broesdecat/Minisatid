#include "solvers/aggsolver/AggComb.hpp"

#include "solvers/aggsolver/AggSolver.hpp"

#include <algorithm>

using namespace Aggrs;

bool Aggrs::isNeutralElement(const Weight& w, AggrType t){
	if(t==MAX || t==MIN){
		return false;
	}else if(t==SUM || t==CARD){
		return w==0;
	}else if(t==PROD){
		return w==1;
	}
}

AggSet::AggSet(const vector<Lit>& lits, const vector<Weight>& weights){
	for(int i=0; i<lits.size(); i++){
		wlits.push_back(WL(lits[i], weights[i]));
	}
	std::sort(wlits.begin(), wlits.end());
}

void AggSet::setWL(const vector<WL>& newset){
	wlits.clear();
	wlits.insert(wlits.begin(), newset.begin(), newset.end());
	//important to sort again to guarantee that it is sorted according to the weights
	std::sort(wlits.begin(), wlits.end());
}

AggComb::AggComb(const paggsol& solver, const vector<Lit>& lits, const vector<Weight>& weights):
		aggsolver(solver), set(new AggSet(lits, weights)){
}

AggComb::~AggComb(){
	deleteList<Agg>(aggregates);
	delete set;
};

FWAgg::FWAgg(const paggsol& solver, const vector<Lit>& lits, const vector<Weight>& weights):
		AggComb(solver, lits, weights), currentbestcertain(0),currentbestpossible(0),emptysetvalue(0){
}

rClause FWAgg::propagate(const Lit& p, const Watch& ws){
	Occurrence tp;
    if (ws.getType()==POS){
    	tp = sign(p)? NEG : POS;
    }else{
    	tp = sign(p)? POS : NEG;
    }

    const WL& wl = getWL()[ws.getIndex()];
	stack.push_back(PropagationInfo(p, wl.getWeight(), tp, getCC(), getCP()));
	truth[ws.getIndex()] = tp==POS?l_True:l_False;
	tp==POS? addToCertainSet(wl):removeFromPossibleSet(wl);

	rClause confl = nullPtrClause;
	for(vpagg::const_iterator i=getAgg().begin(); i<getAgg().end() && confl == nullPtrClause; i++){
		const Agg& pa = **i;

		//TODO dit is vrij lelijk
		if(getSolver()->verbosity()>=4){
			reportf("Propagating into aggr: ");
			Aggrs::printAgg(pa);
		}

		lbool hv = headvalue[pa.getIndex()];
		if(hv != l_Undef){ //head is already known
			assert(canPropagateHead(pa, getCC(), getCP())!=(hv==l_True?l_False:l_True));	//A conflicting propagation is not possible if we have complete propagation
			confl = propagate(pa, hv==l_True);
		}else{ //head is not yet known, so at most the head can be propagated
			lbool result = canPropagateHead(pa, getCC(), getCP());
			if(result!=l_Undef){
				rClause cc = getSolver()->notifySATsolverOfPropagation(result==l_True?pa.getHead():~pa.getHead(), new AggReason(pa, p, CPANDCC, true));
				confl = cc;
			}
		}
	}
	return confl;
}

/*
 * Allow sorting of WL, getting same literals next to each other
 */
bool compareLits(const WL& one, const WL& two) {
	return var(one.getLit())<var(two.getLit());
}

/**
 * Checks whether the same literal occurs multiple times in the set
 * If this is the case, all identical literals are combined into one.
 *
 * @post: the literals are sorted according to weight again
 */
void AggComb::doSetReduction() {
	vwl oldset = getSet()->getWL();
	vwl newset;

	//Sort all wlits according to the integer representation of their literal (to get all literals next to each other)
	std::sort(oldset.begin(), oldset.end(), compareLits);

	int indexinnew = 0;
	newset.push_back(oldset[indexinnew]);

	bool setisreduced = false;
	for(vwl::size_type i=1; i<oldset.size(); i++){
		WL oldl = newset[indexinnew];
		WL newl = oldset[i];
		if(var(oldl.getLit())==var(newl.getLit())){ //same variable
			setisreduced = true;
			if(oldl.getLit()==newl.getLit()){ //same literal, keep combined weight
				Weight w = getCombinedWeight(newl.getWeight(), oldl.getWeight());
				newset[indexinnew] = WL(oldl.getLit(), w);
			}else{ //opposite signs
				WL wl = handleOccurenceOfBothSigns(oldl, newl);
				newset[indexinnew] = WL(wl.getLit(), wl.getWeight());
			}
		}else{
			newset.push_back(newl);
			indexinnew++;
		}
	}

	vwl newset2;
	for(vwl::size_type i=0; i<newset.size(); i++){
		if(!isNeutralElement(newset[i].getWeight(), getType())){
			newset2.push_back(newset[i]);
		}else{
			setisreduced = true;
		}
	}

	if(setisreduced){
		getSet()->setWL(newset2);
	}
}

pcomb FWAgg::initialize(bool& unsat){
	unsat = false;
	if(getAgg().size()==0){
		return NULL;
	}
	doSetReduction();
	truth.resize(getWL().size(), l_Undef);

	setCP(getBestPossible());
	setCC(getESV());

	int startsize = aggregates.size();
	headvalue.resize(startsize, l_Undef);
	headindex.resize(startsize, -1);
	nomoreprops.resize(startsize, false);
	optimagg.resize(startsize, false);
	headproptime.resize(startsize, -1);
	headprop.resize(startsize, false);

	int i=0, j=0;
	for(; !unsat && i<aggregates.size(); i++){
		Agg* agg = aggregates[i];
		lbool result = initialize(*agg);
		if(result==l_True){
			//If after initialization, the head will have a fixed value, then this is
			//independent of any further propagations within that aggregate.
			getSolver()->removeHeadWatch(var(agg->getHead()));
			delete agg;
		}else if(result==l_False){
			//UNSAT because always false
			unsat = true;
		}else{
			agg->setIndex(j);
			aggregates[j++] = agg;
		}
	}
	aggregates.resize(j);

	headvalue.resize(j, l_Undef);
	headindex.resize(j, -1);
	nomoreprops.resize(j, false);
	optimagg.resize(j, false);
	headproptime.resize(j, -1);
	headprop.resize(j, false);

	for (int j = 0; j< getWL().size(); j++) {
		const Lit& l = getWL()[j].getLit();
		Var v = var(l);
		getSolver()->addPermWatch(v, new Watch(this, j, true, sign(l) ? false : true));
	}

	return this;
}

/**
 * Returns true if this aggregate can be propagated in the initialization, so it will never change truth value
 * and can be left out of any propagations.
 */
lbool FWAgg::initialize(const Agg& agg){
	rClause confl = nullPtrClause;

	lbool hv = canPropagateHead(agg, getCC(), getCP());
	bool alwaystrue = false;
	if(hv!=l_Undef && !optimagg[agg.getIndex()]){
		alwaystrue = true;
		//reportf("No more propagations for %d", gprintVar(var(head)));
	}
	if(hv==l_True){
		confl = getSolver()->notifySATsolverOfPropagation(agg.getHead(), new AggReason(agg, agg.getHead(), CPANDCC, true));
	}else if(hv==l_False){
		confl = getSolver()->notifySATsolverOfPropagation(~agg.getHead(), new AggReason(agg, ~agg.getHead(), CPANDCC, true));
	}
	if(confl!=nullPtrClause){
		return l_False;
	}

	return alwaystrue?l_True:l_Undef;
}

void FWAgg::backtrack(const Agg& agg, int stacksize){
	if(headprop[agg.getIndex()] && headproptime[agg.getIndex()]>stacksize){
		headprop[agg.getIndex()] = false;
	}
}

void FWAgg::backtrack(const Agg& agg){
	if(nomoreprops[agg.getIndex()]){ return; }

	headvalue[agg.getIndex()] = l_Undef;
	headindex[agg.getIndex()] = -1;
}


void FWAgg::backtrack(const Watch& w) {
	if (getStack().size()==0 || var(getStack().back().getLit())!=var(getWL()[w.getIndex()].getLit())) {
		return;	//Only backtrack if it was effectively propagated
	}
	const PropagationInfo& pi = stack.back();
	stack.pop_back();

	assert(pi.getType()!=HEAD && var(pi.getLit())==var(getWL()[w.getIndex()].getLit()));

	truth[w.getIndex()] = l_Undef;
	setCC(pi.getPC());
	setCP(pi.getPP());

	int s = stack.size();
	for(vpagg::const_iterator i=getAgg().begin(); i<getAgg().end(); i++){
		backtrack(**i, s);
	}
}

/*

/**
 * Returns non-owning pointer
 */
rClause FWAgg::propagate(const Agg& agg, bool headtrue){
	if(nomoreprops[agg.getIndex()] || headprop[agg.getIndex()]){ return nullPtrClause; }

	headvalue[agg.getIndex()] = headtrue?l_True:l_False;
	headindex[agg.getIndex()] = getStack().size();
	rClause confl = propagate(agg, headtrue);
	return confl;
}

lbool FWAgg::canPropagateHead(const Agg& agg, const Weight& CC, const Weight& CP) const{
	if(nomoreprops[agg.getIndex()] || headprop[agg.getIndex()]){ return headvalue[agg.getIndex()]; }

	if ((agg.isLower() && CC > agg.getLowerBound()) || (agg.isUpper() && CP < agg.getUpperBound())) {
		headproptime[agg.getIndex()] = getStack().size();
		headprop[agg.getIndex()] = true;
		return l_False;
	} else if ((agg.isLower() && CP <= agg.getLowerBound()) || (agg.isUpper() && CC >= agg.getUpperBound())) {
		headproptime[agg.getIndex()] = getStack().size();
		headprop[agg.getIndex()] = true;
		return l_True;
	} else {
		return l_Undef;
	}
}

/**
 * Should find a set L+ such that "bigwedge{l | l in L+} implies p"
 * which is equivalent with the clause bigvee{~l|l in L+} or p
 * and this is returned as the set {~l|l in L+}
 */
void FWAgg::getExplanation(vec<Lit>& lits, const AggReason& ar) const{
	//assert(ar.getAgg() == agg);
	//assert(agg->getSet()==this);

	const Agg& agg = ar.getAgg();
	const Lit& head = agg.getHead();

	int index = -1;
	for(int i=0; i<getStack().size(); i++){
		if(getStack()[i].getLit()==ar.getLit()){
			index = i;
			break;
		}
	}
	assert(index!=-1);

	if(!ar.isHeadReason() && index >= headindex[agg.getIndex()]){
		//the head literal is saved as it occurred in the theory, so adapt for its current truth value!
		lits.push(getSolver()->isTrue(head)?~head:head);
	}

	//assert(ar.isHeadReason() || getPCSolver()->getLevel(ar.getLit())<=s->getStackSize());

//	This is correct, but not minimal enough. We expect to be able to do better
//	for(lprop::const_iterator i=s->getStackBegin(); counter<ar.getIndex() && i<s->getStackEnd(); i++,counter++){
//		lits.push(~(*i).getLit());
//	}

	int counter = 0;
	if(ar.getExpl()!=HEADONLY){
		for(vprop::const_iterator i=getStack().begin(); counter<index && i<getStack().end(); i++,counter++){
		//for(lprop::const_iterator i=s->getStackBegin(); var(ar.getLit())!=var((*i).getLit()) && i<s->getStackEnd(); i++){
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
			default:
				assert(false);
				break;
			}
		}
	}

	//TODO de nesting van calls is vrij lelijk en onefficient :)
	if(getSolver()->verbosity()>=5){

		reportf("STACK: ");
		for(vprop::const_iterator i=getStack().begin(); i<getStack().end(); i++){
			gprintLit((*i).getLit()); reportf(" ");
		}
		reportf("\n");


		reportf("Aggregate explanation for ");
		if(ar.isHeadReason()){
			gprintLit(head);
		}else{
			reportf("(index %d)", index);
			gprintLit((*(getWL().begin()+index)).getLit());
		}

		reportf(" is");
		for(int i=0; i<lits.size(); i++){
			reportf(" ");
			gprintLit(lits[i]);
		}
		reportf("\n");
	}
}

/*****************
 * MAX AGGREGATE *
 *****************/

MaxFWAgg::MaxFWAgg(const paggsol& solver, const vector<Lit>& lits, const vector<Weight>& weights):
		FWAgg(solver, lits, weights){
	//FIXME moet eigenlijk een voorstelling van -infinity zijn
	//ik had eerst: |minimum van de set| -1, maar de bound zelf kan NOG lager liggen, dus dan is het fout
	emptysetvalue = Weight(INT_MIN);
	assert(emptysetvalue<=INT_MIN);
}

Weight MaxFWAgg::getBestPossible() const{
	return getWL().back().getWeight();
}

void MaxFWAgg::addToCertainSet(const WL& l){
	if(l.getWeight()>getCC()){
		setCC(l.getWeight());
	}
}

void MaxFWAgg::removeFromPossibleSet(const WL& l){
	if(l.getWeight()==getCP()){
		bool found = false;
		for(int i=0; i<getWL().size(); i++){
			if(truth[i] != l_False){
				setCP(getWL()[i].getWeight());
				found = true;
			}
		}
		if(!found){
			setCP(getESV());
		}
	}
}

Weight MaxFWAgg::getCombinedWeight(const Weight& first, const Weight& second) const{
	return first>second?first:second;
}

WL MaxFWAgg::handleOccurenceOfBothSigns(const WL& one, const WL& two){
	if(one.getWeight()>two.getWeight()){
		if(getESV()<two.getWeight()){
			setESV(two.getWeight());
		}
		return one;
	}else{
		if(getESV()<one.getWeight()){
			setESV(one.getWeight());
		}
		return two;
	}
}

bool MaxFWAgg::isMonotone(const Agg& agg, const WL& l) const{
	return (agg.isLower() && l.getWeight()<=agg.getLowerBound())
				|| (agg.isUpper() && l.getWeight()>=agg.getUpperBound());
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
rClause MaxFWAgg::propagate(const Agg& agg, bool headtrue) {
	//TODO if(nomoreprops || headprop){ return nullPtrClause; }

	rClause confl = nullPtrClause;
	if (headtrue && agg.isLower()) {
		for(vwl::const_reverse_iterator i=getWL().rbegin(); confl == nullPtrClause && i<getWL().rend() && agg.getLowerBound()<(*i).getWeight(); i++){
			//because these propagations are independent of the other set literals, they can also be written as clauses
			confl = getSolver()->notifySATsolverOfPropagation(~(*i).getLit(), new AggReason(agg,~(*i).getLit(),HEADONLY));
		}
	}else if(!headtrue && agg.isUpper()){
		for(vwl::const_reverse_iterator i=getWL().rbegin(); confl == nullPtrClause && i<getWL().rend() && agg.getUpperBound()<=(*i).getWeight(); i++){
			confl = getSolver()->notifySATsolverOfPropagation(~(*i).getLit(), new AggReason(agg,~(*i).getLit(),HEADONLY));
		}
	}
	if(confl==nullPtrClause){
		confl = propagateAll(agg, headtrue);
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
rClause MaxFWAgg::propagateAll(const Agg& agg, bool headtrue) {
	rClause confl = nullPtrClause;

	//TODO if(nomoreprops || headprop){ return confl; }

	if((agg.isLower() && headtrue) || (agg.isUpper() && !headtrue)){
		return confl;
	}

	int pos = -1;
	bool exactlyoneleft = true;
	for(int i=0; exactlyoneleft && i<getWL().size(); i++){
		const WL& wl = getWL()[i];
		if((agg.isUpper() && headtrue && wl.getWeight()>=agg.getUpperBound())
					|| (agg.isLower() && !headtrue && wl.getWeight()>agg.getLowerBound())){
			if(truth[i]==l_Undef){
				if(pos!=-1){
					exactlyoneleft = false;
				}else{
					pos = i;
				}
			}else if(truth[i]==l_True){
				exactlyoneleft = false;
			}
		}
	}
	if(exactlyoneleft){
		//TODO BASEDONCP is not correct enough (ONCPABOVEBOUND)
		confl = getSolver()->notifySATsolverOfPropagation(getWL()[pos].getLit(), new AggReason(agg, getWL()[pos].getLit(), BASEDONCP));
	}
	return confl;
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
bool MaxFWAgg::canJustifyHead(const Agg& agg, vec<Lit>& jstf, vec<Var>& nonjstf, vec<int>& currentjust, bool real) const {
	bool justified = false;
	if(agg.isLower()){
		for(vwl::const_reverse_iterator i=getWL().rbegin(); i<getWL().rend() && (*i).getWeight()>agg.getLowerBound(); i++) {
			if(oppositeIsJustified(*i, currentjust, real)){
				jstf.push(~(*i).getLit()); //push negative literal, because it should become false
			}else if(real ||currentjust[var((*i).getLit())]!=0){
				nonjstf.push(var((*i).getLit()));
			}
		}
		if(nonjstf.size()==0){
			justified = true;
		}
	}else{
		for(vwl::const_reverse_iterator i=getWL().rbegin(); i<getWL().rend() && (*i).getWeight()>=agg.getUpperBound(); i++) {
			if(isJustified(*i, currentjust, real)){
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

/************************
 * RECURSIVE AGGREGATES *
 ************************/

/**
 * Important: to justify a head, often several body literals have to become FALSE
 * For such literals, they have to be justified if they are NEGATIVE
 *
 * Also, if a literal has to become FALSE, its INVERSION should be added to the justification!
 */
bool AggComb::oppositeIsJustified(const WL& l, vec<int>& currentjust, bool real) const{
	if(real){
		return getSolver()->value(l.getLit())!=l_True;
	}else{
		return getSolver()->value(l.getLit())!=l_True && (!sign(l.getLit()) || isJustified(var(l.getLit()), currentjust));
	}
}

bool AggComb::isJustified(const WL& l, vec<int>& currentjust, bool real) const{
	if(real){
		return getSolver()->value(l.getLit())!=l_False;
	}else{
		return getSolver()->value(l.getLit())!=l_False && (sign(l.getLit()) || isJustified(var(l.getLit()), currentjust));
	}
}

bool AggComb::isJustified(Var x, vec<int>& currentjust) const{
	return currentjust[x]==0;
}

///////
//PW Aggregates
///////

PWAgg::PWAgg(const paggsol& solver, const vector<Lit>& lits, const vector<Weight>& weights):
		AggComb(solver, lits, weights){
}

CardPWAgg::CardPWAgg(const paggsol& solver, const vector<Lit>& lits, const vector<Weight>& weights):
			PWAgg(solver, lits, weights), emptysetvalue(0){
}

rClause CardPWAgg::propagate(const Lit& p, const Watch& w){

};

rClause CardPWAgg::propagate(const Agg& agg, bool headtrue){

};

void CardPWAgg::getExplanation(vec<Lit>& lits, const AggReason& ar) const{

};

pcomb CardPWAgg::initialize	(bool& unsat){

};

Weight CardPWAgg::getCombinedWeight(const Weight& one, const Weight& two) 	const{
	return one+two;
};

WL CardPWAgg::handleOccurenceOfBothSigns(const WL& one, const WL& two){
	if(one.getWeight()>two.getWeight()){
		setESV(getESV() + two.getWeight());
		return WL(one.getLit(), one.getLit()-two.getLit());
	}else{
		setESV(getESV() + one.getWeight());
		return WL(one.getLit(), two.getLit()-one.getLit());
	}
};

bool CardPWAgg::canJustifyHead(const Agg& agg, vec<Lit>& jstf, vec<Var>& nonjstf, vec<int>& currentjust, bool real) const{

};

///////
// DEBUG
///////

void Aggrs::printAgg(AggComb const * const c, bool endl){
	reportf("%s{", c->getName().c_str());
	for (vwl::const_iterator i=c->getWL().begin(); i<c->getWL().end(); ++i) {
		reportf(" "); gprintLit((*i).getLit()); reportf("(%s)",printWeight((*i).getWeight()).c_str());
	}
	if(endl){
		reportf(" }\n");
	}else{
		reportf(" }");
	}
}

void Aggrs::printAgg(const Agg& ae){
	gprintLit(ae.getHead());
	pcomb set = ae.getAggComb();
	if(ae.isLower()){
		reportf(" <- ");
	}else{
		reportf(" <- %s <= ", printWeight(ae.getUpperBound()).c_str());
	}
	printAgg(set, false);
	if(ae.isLower()){
		//reportf(" <= %s. Known values: bestcertain=%s, bestpossible=%s\n", printWeight(ae.getLowerBound()).c_str(), printWeight(set->getCC()).c_str(), printWeight(set->getCP()).c_str());
		reportf(" <= %s.\n", printWeight(ae.getLowerBound()).c_str());
	}else{
		//reportf(". Known values: bestcertain=%s, bestpossible=%s\n", printWeight(set->getCC()).c_str(), printWeight(set->getCP()).c_str());
		reportf(".\n");
	}
}
