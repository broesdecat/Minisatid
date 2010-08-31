#include "solvers/aggsolver/AggComb.hpp"

#include "solvers/aggsolver/AggSolver.hpp"

#include <algorithm>

using namespace Aggrs;

AggSet::AggSet(const vector<WL>& wl){
	wlits.insert(wlits.begin(), wl.begin(), wl.end());
	std::sort(wlits.begin(), wlits.end());
}

void AggSet::setWL(const vector<WL>& newset){
	wlits=newset;
	//important to sort again to guarantee that it is sorted according to the weights
	std::sort(wlits.begin(), wlits.end());
}

AggComb::AggComb(const paggsol& solver, const vector<WL>& wl):
		aggsolver(solver), set(new AggSet(wl)), emptysetvalue(0){
}

const WL& Watch::getWL()	const {
	return agg->getWL()[index];
}

const WL& PWWatch::getWL()	const {
	return dynamic_cast<CardPWAgg*>(agg)->getWatched()[index];
}

void AggComb::addAgg(pagg aggr){
	aggregates.push_back(aggr);
	aggr->setComb(this, aggregates.size()-1);
}

void FWAgg::addAgg(pagg aggr){
	int startsize = aggregates.size()+1;
	headvalue.resize(startsize, l_Undef);
	headindex.resize(startsize, -1);
	nomoreprops.resize(startsize, false);
	optimagg.resize(startsize, false);
	headproptime.resize(startsize, -1);
	headprop.resize(startsize, false);
	AggComb::addAgg(aggr);
}

/*AggComb::AggComb(const AggComb& comb){
	aggregates = comb.getAgg();
	set = comb.getSet();
	aggsolver = comb.getSolver();
	emptysetvalue = comb.getESV();
}*/

AggComb::~AggComb(){
	deleteList<Agg>(aggregates);
	delete set;
};

FWAgg::FWAgg(const paggsol& solver, const vwl& wl):
	AggComb(solver, wl), currentbestcertain(0), currentbestpossible(0){

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
		if(!isNeutralElement(newset[i].getWeight())){
			newset2.push_back(newset[i]);
		}else{
			setisreduced = true;
		}
	}

	if(setisreduced){
		getSet()->setWL(newset2);
	}
}

// Final initialization call!
// @post: returns NULL if no more aggregates present!
pcomb AggComb::initialize(bool& unsat){
	for(int i=0; i<getAgg().size(); i++){
		getSolver()->setHeadWatch(var(getAgg()[i]->getHead()), getAgg()[i]);
	}
	return getAgg().size()==0?NULL:this;
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

	int i=0, j=0;
	for(; !unsat && i<aggregates.size(); i++){
		pagg agg = aggregates[i];
		lbool result = initialize(*agg);
		if(result==l_True && !agg->isDefined()){
			//If after initialization, the head will have a fixed value, then this is
			//independent of any further propagations within that aggregate.
			//BUT ONLY if it is not defined (or at a later stage, if it cannot be in any loop
			getSolver()->removeHeadWatch(var(agg->getHead()));
			delete agg;
		}else if(result==l_False){
			//UNSAT because always false
			unsat = true;
			return NULL;
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

	pcomb newagg = AggComb::initialize(unsat);

	if(newagg==this){
		for (int j = 0; j< getWL().size(); j++) {
			const Lit& l = getWL()[j].getLit();
			Var v = var(l);
			getSolver()->addPermWatch(v, new Watch(this, j, true, sign(l) ? false : true));
		}
	}

	return newagg;
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
		confl = getSolver()->notifySolver(agg.getHead(), new AggReason(agg, agg.getHead(), CPANDCC, true));
	}else if(hv==l_False){
		confl = getSolver()->notifySolver(~agg.getHead(), new AggReason(agg, ~agg.getHead(), CPANDCC, true));
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
	if (getStack().size()==0 || var(getStack().back().getLit())!=var(w.getWL().getLit())) {
		return;	//Only backtrack if it was effectively propagated
	}
	const PropagationInfo& pi = stack.back();
	stack.pop_back();

	assert(pi.getType()!=HEAD && var(pi.getLit())==var(w.getWL().getLit()));

	truth[w.getIndex()] = l_Undef;
	setCC(pi.getPC());
	setCP(pi.getPP());

	int s = stack.size();
	for(vpagg::const_iterator i=getAgg().begin(); i<getAgg().end(); i++){
		backtrack(**i, s);
	}
}

/**
 * Returns non-owning pointer
 */
rClause FWAgg::propagate(const Agg& agg){
	//TODO er is iets mis met headvalue, headprop etc!
	if(nomoreprops[agg.getIndex()] || headvalue[agg.getIndex()]!=l_Undef){ return nullPtrClause; }

	lbool headtrue = getSolver()->value(agg.getHead());
	headvalue[agg.getIndex()] = headtrue;
	headindex[agg.getIndex()] = getStack().size();
	rClause confl = propagate(agg, headtrue==l_True);
	return confl;
}

rClause FWAgg::propagate(const Lit& p, const Watch& ws){
	Occurrence tp;
    if (ws.getType()==POS){
    	tp = sign(p)? NEG : POS;
    }else{
    	tp = sign(p)? POS : NEG;
    }

    const WL& wl = ws.getWL();
	stack.push_back(PropagationInfo(p, wl.getWeight(), tp, getCC(), getCP()));
	truth[ws.getIndex()] = tp==POS?l_True:l_False;
	tp==POS? addToCertainSet(wl):removeFromPossibleSet(wl);

	rClause confl = nullPtrClause;
	for(vpagg::const_iterator i=getAgg().begin(); i<getAgg().end() && confl == nullPtrClause; i++){
		const Agg& pa = **i;

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
				rClause cc = getSolver()->notifySolver(result==l_True?pa.getHead():~pa.getHead(), new AggReason(pa, p, CPANDCC, true));
				confl = cc;
			}
		}
	}
	return confl;
}

lbool FWAgg::canPropagateHead(const Agg& agg, const Weight& CC, const Weight& CP) const{
	if(nomoreprops[agg.getIndex()] || headprop[agg.getIndex()]){ return headvalue[agg.getIndex()]; }

	if ((agg.isLower() && CC > agg.getLowerBound()) || (agg.isUpper() && CP < agg.getUpperBound())) {
		if(!optimagg[agg.getIndex()]){ // TODO niet de mooiste oplossing: bij optimagg geen headprop gebruiken want die is toch fout als de bound wordt aangepast
			headproptime[agg.getIndex()] = getStack().size();
			headprop[agg.getIndex()] = true;
		}
		return l_False;
	} else if ((agg.isLower() && CP <= agg.getLowerBound()) || (agg.isUpper() && CC >= agg.getUpperBound())) {
		if(!optimagg[agg.getIndex()]){
			headproptime[agg.getIndex()] = getStack().size();
			headprop[agg.getIndex()] = true;
		}
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

	int index = -1;
	for(int i=0; i<getStack().size(); i++){
		if(getStack()[i].getLit()==ar.getLit()){
			index = i;
			break;
		}
	}
	if(index==-1){
		index = getStack().size();
	}
	//assert(index!=-1); //Is wrong because when a conflict is derived, an explanation is constructed before the conflicting literal is stacked.

	const Agg& agg = ar.getAgg();
	const Lit& head = agg.getHead();

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

MaxFWAgg::MaxFWAgg(const paggsol& solver, const vector<WL>& wl):
		FWAgg(solver, wl){
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
			confl = getSolver()->notifySolver(~(*i).getLit(), new AggReason(agg,~(*i).getLit(),HEADONLY));
		}
	}else if(!headtrue && agg.isUpper()){
		for(vwl::const_reverse_iterator i=getWL().rbegin(); confl == nullPtrClause && i<getWL().rend() && agg.getUpperBound()<=(*i).getWeight(); i++){
			confl = getSolver()->notifySolver(~(*i).getLit(), new AggReason(agg,~(*i).getLit(),HEADONLY));
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
		confl = getSolver()->notifySolver(getWL()[pos].getLit(), new AggReason(agg, getWL()[pos].getLit(), BASEDONCP));
	}
	return confl;
}

SPFWAgg::SPFWAgg(const paggsol& solver, const vector<WL>& wl)
		:FWAgg(solver, wl){
}

Weight SPFWAgg::getCombinedWeight(const Weight& one, const Weight& two) const {
	return this->add(one, two);
}

Weight SPFWAgg::getBestPossible() const{
	Weight max = getESV();
	for (vwl::const_iterator j = getWL().begin(); j < getWL().end(); j++) {
		max = this->add(max, (*j).getWeight());
	}
	return max;
}

void SPFWAgg::addToCertainSet(const WL& l){
	setCC(this->add(getCC(), l.getWeight()));
}

void SPFWAgg::removeFromPossibleSet(const WL& l){
	setCP(this->remove(getCP(), l.getWeight()));
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
rClause SPFWAgg::propagate(const Agg& agg, bool headtrue){
	if(nomoreprops[agg.getIndex()] || headprop[agg.getIndex()]){ return nullPtrClause; }

	return propagateAll(agg, headtrue);
}

/**
 * Returns non-owning pointer
 */
rClause SPFWAgg::propagateAll(const Agg& agg, bool headtrue){
	if(nomoreprops[agg.getIndex()] || headprop[agg.getIndex()]){ return nullPtrClause; }

	rClause c = nullPtrClause;
	Weight weightbound(0);

	Expl basedon = CPANDCC;

	//determine the lower bound of which weight literals to consider
	if (headtrue) {
		if(agg.isLower()){
			basedon = BASEDONCC;
			weightbound = remove(agg.getLowerBound(), getCC());
			//+1 because larger and not eq
			if(add(weightbound, getCC())==agg.getLowerBound()){
				weightbound+=1;
			}
		}else{
			basedon = BASEDONCP;
			weightbound = remove(getCP(), agg.getUpperBound());
			//+1 because larger and not eq
			if(this->add(weightbound, agg.getUpperBound())==getCP()){
				weightbound+=1;
			}
		}
	} else {
		if(agg.isLower()){
			basedon = BASEDONCP;
			weightbound = remove(getCP(), agg.getLowerBound());
		}else{
			basedon = BASEDONCC;
			weightbound = remove(agg.getUpperBound(), getCC());
		}
	}

#ifdef INTWEIGHT
	if(weightbound == INT_MAX || weightbound == INT_MIN){
		return c;
	}
#endif

	vwl::const_iterator pos = lower_bound(getWL().begin(), getWL().end(), weightbound);
	if(pos==getWL().end()){
		return c;
	}

	//find the index of the literal
	int start = 0;
	vwl::const_iterator it = getWL().begin();
	while(it!=pos){
		it++; start++;
	}

	for(int u = start; c==nullPtrClause && u < getWL().size(); u++) {
		if(truth[u]==l_Undef){//if already propagated as an aggregate, then those best-values have already been adapted
			const Lit& l = getWL()[u].getLit();
			if((agg.isLower() && headtrue) || (agg.isUpper() && !headtrue)){
				c = getSolver()->notifySolver(~l, new AggReason(agg, ~l, basedon));
			}else{
				c = getSolver()->notifySolver(l, new AggReason(agg, l, basedon));
			}
		}
	}
	return c;
}

SumFWAgg::SumFWAgg(const paggsol& solver, const vector<WL>& lw)
		:SPFWAgg(solver, lw){
	emptysetvalue = 0;
}

pcomb SumFWAgg::initialize(bool& unsat){
	unsat = false;
	if(aggregates.size()==0){
		return NULL;
	}

	// Transform the sum into one only containing natural numbers.
	vwl wlits2;
	Weight totalneg(0);
	for(vwl::const_iterator i=getWL().begin(); i<getWL().end(); i++){
		if ((*i).getWeight() < 0) {
			totalneg-=(*i).getWeight();
		}
	}
	if(totalneg > 0){
		for(vwl::const_iterator i=getWL().begin(); i<getWL().end(); i++){
			wlits2.push_back(WL((*i).getLit(), abs((*i).getWeight())));
		}
		getSet()->setWL(wlits2);
		for(vpagg::const_iterator i=getAgg().begin(); i<getAgg().end(); i++){
			addToBounds(**i, totalneg);
		}
	}

	//Test whether the total sum of the weights does not overflow for integer weights
#ifdef INTWEIGHT

	Weight total(0);
	for(vwl::const_iterator i=getWL().begin(); i<getWL().end(); i++){
		if(INT_MAX-total < (*i).getWeight()){
			throw idpexception("The total sum of weights exceeds max-int, correctness cannot be guaranteed in limited precision.\n");
		}
		total += (*i).getWeight();
	}
#endif

	return FWAgg::initialize(unsat);
}

WL SumFWAgg::handleOccurenceOfBothSigns(const WL& one, const WL& two){
	if(one.getWeight()<two.getWeight()){
		setESV(getESV() + one.getWeight());
		return WL(two.getLit(), this->remove(two.getWeight(), one.getWeight()));
	}else{
		setESV(getESV() + two.getWeight());
		return WL(one.getLit(), this->remove(one.getWeight(), two.getWeight()));
	}
}

bool SumFWAgg::isMonotone(const Agg& agg, const WL& l) const{
	return (agg.isLower() && l.getWeight()<0) || (agg.isUpper() && l.getWeight()>0);
}

/**
 * This method returns a reason clause that is currently false and that explains why the current optimizing
 * sum aggregate is violated. This can serve as a learned clause to backtrack during optimization search.
 */
void SumFWAgg::getMinimExplan(const Agg& agg, vec<Lit>& lits){
	Weight certainsum = getESV();
	Weight possiblesum = getBestPossible();

	bool explained = false;
	if((agg.isLower() && certainsum>agg.getLowerBound())
			|| (agg.isUpper() && certainsum>=agg.getUpperBound())
			|| (agg.isLower() && possiblesum <= agg.getLowerBound())
			|| (agg.isUpper() && possiblesum < agg.getUpperBound())){
		explained = true;
	}

	for(vprop::const_iterator i=getStack().begin(); !explained && i<getStack().end(); i++){
		bool push = false;
		if((*i).getType() == POS){ //means that the literal in the set became true
			certainsum += (*i).getWeight();

			if(agg.isLower()){
				push = true;
				if(agg.getLowerBound() < certainsum){
					explained = true;
				}
			}
		}else if((*i).getType() == NEG){ //the literal in the set became false
			possiblesum -= (*i).getWeight();

			if(agg.isUpper()){
				push = true;
				if(possiblesum < agg.getUpperBound()){
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

void SumFWAgg::addToBounds(Agg& agg, const Weight& w){
	if(agg.isLower()){
		agg.setLowerBound(add(agg.getLowerBound(), w));
	}else{
		agg.setUpperBound(add(agg.getUpperBound(), w));
	}
}

ProdFWAgg::ProdFWAgg(const paggsol& solver, const vector<WL>& wl)
		:SPFWAgg(solver, wl){
	emptysetvalue = 1;
}

pcomb ProdFWAgg::initialize(bool& unsat){
	unsat = false;
	if(aggregates.size()==0){
		return NULL;
	}
#ifdef INTWEIGHT
	//Test whether the total product of the weights is not infinity for intweights
	Weight total(1);
	for(vwl::const_iterator i=getWL().begin(); i<getWL().end(); i++){
		if(INT_MAX/total < (*i).getWeight()){
			throw idpexception("The total product of weights exceeds max-int, correctness cannot be guaranteed in limited precision.\n");
		}
		total *= (*i).getWeight();
	}
#endif

	return FWAgg::initialize(unsat);
}

WL ProdFWAgg::handleOccurenceOfBothSigns(const WL& one, const WL& two){
	//NOTE: om dit toe te laten, ofwel bij elke operatie op en literal al zijn voorkomens overlopen
	//ofwel aggregaten voor doubles ondersteunen (het eerste is eigenlijk de beste oplossing)
	//Mogelijke eenvoudige implementatie: weigts bijhouden als doubles (en al de rest als ints)
	reportf("Product aggregates in which both the literal and its negation occur "
			"are currently not supported. Replace ");
	gprintLit(one.getLit()); reportf("or "); gprintLit(two.getLit()); reportf("by a tseitin.\n");
	throw idpexception("Atoms in product aggregates have to be unique.\n");
}

bool ProdFWAgg::isMonotone(const Agg& agg, const WL& l) const{
	assert(l.getWeight()==0 || l.getWeight()>=1);
	return agg.isUpper();
}

Weight SumCalc::add(const Weight& lhs, const Weight& rhs) const{
#ifdef INTWEIGHT
	if(lhs>0 && rhs > 0 && INT_MAX-lhs < rhs){
		return INT_MAX;
	}else if(lhs<0 && rhs<0 && INT_MIN-lhs>rhs){
		return INT_MIN;
	}
#endif
	return lhs+rhs;
}

Weight SumCalc::remove(const Weight& lhs, const Weight& rhs) const{
	return lhs-rhs;
}

Weight ProdCalc::add(const Weight& lhs, const Weight& rhs) const{
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

Weight ProdCalc::remove(const Weight& lhs, const Weight& rhs) const{
	Weight w = 0;
	if(rhs!=0){
		w = lhs/rhs;
		if(w==1 && lhs>rhs){
			w=2;
		}
	}

	return w;
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
bool MaxFWAgg::canJustifyHead( const Agg& agg, vec<Lit>& jstf, vec<Var>& nonjstf, vec<int>& currentjust, bool real) const {
	AggrType type = agg.getAggComb()->getType();
	bool justified = false;
	const vwl& wl = getWL();

	if(agg.isLower()){
		for(vwl::const_reverse_iterator i=wl.rbegin(); i<wl.rend() && (*i).getWeight()>agg.getLowerBound(); i++) {
			if(oppositeIsJustified(*i, currentjust, real, getSolver())){
				jstf.push(~(*i).getLit()); //push negative literal, because it should become false
			}else if(real ||currentjust[var((*i).getLit())]!=0){
				nonjstf.push(var((*i).getLit()));
			}
		}
		if(nonjstf.size()==0){
			justified = true;
		}
	}else{
		for(vwl::const_reverse_iterator i=wl.rbegin(); i<wl.rend() && (*i).getWeight()>=agg.getUpperBound(); i++) {
			if(isJustified(*i, currentjust, real, getSolver())){
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
 * AGG <= B: v is justified if one literal below/eq the bound is THAT IS NOT THE HEAD
 * 					if so, change the justification to the literal
 * 					otherwise, add all nonfalse, non-justified, relevant, below the bound literals to the queue
 * A <= AGG: v is justified if the negation of all literals below the bound are. The emptyset is always a solution,
 * 			 so no conclusions have to be drawn from the literals above/eq the bound
 * 					if so, change the justification to the negation of all those below the bound literals
 * 					otherwise, add all nonfalse, non-justified, relevant, below the bound literals to the queue
 */
bool SPFWAgg::canJustifyHead(const Agg& agg, vec<Lit>& jstf, vec<Var>& nonjstf, vec<int>& currentjust, bool real) const {
	AggrType type = agg.getAggComb()->getType();
	bool justified = false;
	const vwl& wl = getWL();

	if(agg.isLower()){
		Weight bestpossible = getBestPossible();
		for (vwl::const_iterator i = wl.begin(); !justified && i < wl.end(); ++i) {
			if(oppositeIsJustified(*i, currentjust, real, getSolver())){
				jstf.push(~(*i).getLit());
				bestpossible = remove(bestpossible, (*i).getWeight());
				if (bestpossible <= agg.getLowerBound()){
					justified = true;
				}
			}else if(real ||currentjust[var((*i).getLit())]!=0){
				nonjstf.push(var((*i).getLit()));
			}
		}
	}else{
		Weight bestcertain = getESV();
		for (vwl::const_iterator i = wl.begin(); !justified && i < wl.end(); ++i) {
			if(isJustified(*i, currentjust, real, getSolver())){
				jstf.push((*i).getLit());
				bestcertain = add(bestcertain, (*i).getWeight());
				if (bestcertain >= agg.getUpperBound()){
					justified = true;
				}
			}else if(real ||currentjust[var((*i).getLit())]!=0){
				nonjstf.push(var((*i).getLit()));
			}
		}
	}

	if(getSolver()->verbosity() >=4){
		reportf("Justification checked for ");
		printAgg(agg);

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

/**
 * Important: to justify a head, often several body literals have to become FALSE
 * For such literals, they have to be justified if they are NEGATIVE
 *
 * Also, if a literal has to become FALSE, its INVERSION should be added to the justification!
 */
bool Aggrs::oppositeIsJustified(const WL& l, vec<int>& currentjust, bool real, paggsol solver){
	if(real){
		return solver->value(l.getLit())!=l_True;
	}else{
		return solver->value(l.getLit())!=l_True && (!sign(l.getLit()) || isJustified(var(l.getLit()), currentjust));
	}
}

bool Aggrs::isJustified(const WL& l, vec<int>& currentjust, bool real, paggsol solver){
	if(real){
		return solver->value(l.getLit())!=l_False;
	}else{
		return solver->value(l.getLit())!=l_False && (sign(l.getLit()) || isJustified(var(l.getLit()), currentjust));
	}
}

bool Aggrs::isJustified(Var x, vec<int>& currentjust){
	return currentjust[x]==0;
}

///////
//PW Aggregates
///////

PWAgg::PWAgg(const paggsol& solver, const vector<WL>& wl):
		AggComb(solver, wl){
}

CardPWAgg::CardPWAgg(const paggsol& solver, const vector<WL>& wl):
			PWAgg(solver, wl){
}

pcomb CardPWAgg::initialize	(bool& unsat){
	if(getAgg().size()!=1 || !getAgg()[0]->isUpper() || getSolver()->value(getAgg()[0]->getHead())!=l_True){
		SumFWAgg* s = new SumFWAgg(getSolver(), getWL());
		for(int i=0; i<getAgg().size(); i++) {
			s->addAgg(getAgg()[i]);
		}
		aggregates.clear();
		return s->initialize(unsat);
	}

	//decide on number
	bool headsknown = true;
	const Agg& agg = *getAgg()[0];
	if(getSolver()->value(agg.getHead())==l_Undef){
		headsknown = false;
	}

	if(headsknown){
		numberm = agg.getLowerBound()+1;
	}else{
		numberm = agg.getLowerBound();
	}

	//initialize watch set
	int montaken = 0;
	for(vwl::const_iterator i=getWL().begin(); i<getWL().end(); i++){
		bool monfound = false;
		const Lit& l = (*i).getLit();
		if(montaken<numberm){
			if(isMonotone(agg, *i) && getSolver()->value(l)!=l_False){
				watched.push_back(*i);
				montaken++;
				monfound = true;
			}
		}else if(!monfound){
			rest.push_back(*i);
		}
	}
	if(headsknown && montaken<numberm){
		if(montaken<numberm-1){
			unsat = true;
			return this;	//Not enough monotone, non-false literals to satisfy the aggregate
		}else{
			//can propagate all in the watched set
			for(int i=0; i<watched.size(); i++){
				const Lit& l = watched[i].getLit();
				rClause confl = getSolver()->notifySolver(l, new AggReason(agg, l, BASEDONCC, false));
				if(confl!=nullPtrClause){
					unsat = true;
					return this;
				}
			}
		}
	}else if(!headsknown && montaken<numberm){
		//head is false, propagate it
		rClause confl = getSolver()->notifySolver(~agg.getHead(), new AggReason(agg, ~agg.getHead(), BASEDONCC, true));
		if(confl!=nullPtrClause){
			unsat = true;
			return this;
		}
	}
	for(int i=0; i<watched.size(); i++){
		getSolver()->addTempWatch(~watched[i].getLit(), new PWWatch(this, i, true, false));
	}
	return this;

	/*unsat = false;
	if(getAgg().size()==0){
		return NULL;
	}

	//decide whether to use watched sets
	ws = true;

	//decide on number
	bool lb=false, ub=false, headsknown = true;
	if(getAgg().size()>1){
		throw new idpexception("No implementation for this yet");
	}
	pAgg agg = getAgg()[0];
	if(agg->isLower()){
		lb = true;
	}
	if(agg->isUpper()){
		ub = true;
	}
	if((ub && lb) || (!ub && !lb)){
		throw new idpexception("No implementation for this yet");
	}
	if(getSolver()->value(agg->getHead())==l_Undef){
		headsknown = false;
	}

	if(headsknown && lb){
		numberam = 0;
		numberm = agg->getLowerBound()+1;
	}else if(headsknown && ub){
		numberam = 0;
		numberm = getWL().size()-agg->getUpperBound()+1;
	}else{
		if(lb){
			numberam = getWL().size()-agg->getLowerBound();
			numberm = agg->getLowerBound();
		}else if(ub){
			numberam = agg->getUpperBound();
			numberm = getWL().size()-agg->getUpperBound();
		}
	}

	//initialize watch set
	int montaken = 0, amontaken = 0;
	for(lwlv::const_iterator i=getWL().begin(); i<getWL().end(); i++){
		bool monfound = false, amonfound = false;
		const Lit& l = (*i).getLit();
		if(montaken<numberm){
			if(agg->isMonotone(*i) && getSolver()->value(l)!=l_False){
				watched.push_back(l);
				montaken++;
				monfound = true;
			}else if(!agg->isMonotone(*i) && getSolver()->value(l)!=l_True){
				watched.push_back(~l);
				montaken++;
				monfound = true;
			}
		}else if(!monfound && amontaken<numberam){
			if(!agg->isMonotone(*i) && getSolver()->value(l)!=l_False){
				watched.push_back(l);
				amontaken++;
				amonfound = false;
			}else if(agg->isMonotone(*i) && getSolver()->value(l)!=l_True){
				watched.push_back(~l);
				amontaken++;
				amonfound = false;
			}
		}else if(!monfound && !amonfound){
			nonwatched.push_back(l);
		}
	}
	if(headsknown && montaken<numberm){
		if(montaken<numberm-1){
			unsat = true;
			return this;	//Not enough monotone, non-false literals to satisfy the aggregate
		}else{
			//can propagate all in the watched set
			for(int i=0; i<watched.size(); i++){
				rClause confl = getSolver()->notifySATsolverOfPropagation(watched[i], new AggrReason(agg, watched[i], BASEDONCC, false));
				if(confl!=nullPtrClause){
					unsat = true;
					return this;
				}
			}
		}
	}else if(!headsknown){
		if(montaken<numberm){
			//head is false, propagate it
			rClause confl = getSolver()->notifySATsolverOfPropagation(~agg->getHead(), new AggrReason(agg, ~agg->getHead(), BASEDONCC, true));
			if(confl!=nullPtrClause){
				unsat = true;
				return this;
			}
		}else if(amontaken<numberam){
			//head is true, propagate it
			rClause confl = getSolver()->notifySATsolverOfPropagation(agg->getHead(), new AggrReason(agg, agg->getHead(), BASEDONCC, true));
			if(confl!=nullPtrClause){
				unsat = true;
				return this;
			}
		}
	}
	for(int i=0; i<watched.size(); i++){
		getSolver()->addTempWatch(watched[i], this);
	}
	return this;*/
}

rClause CardPWAgg::propagate(const Lit& p, const Watch& w){
	int ind = 0;
	bool found = false;
	for(; !found && ind<rest.size(); ind++){
		lbool v = getSolver()->value(rest[ind].getLit());
		//reportf("Lit "); gprintLit(rest[ind].getLit()); reportf(" is %s\n", v==l_True?"true": v==l_False?"false":"unkn");
		if(v!=l_False){ // TODO might have been propagated later, check!
			found = true;
			break;
		}
	}

	rClause confl = nullPtrClause;
	if(!found){ // propagate rest
		//reportf("Cannot find replacement, so propagating.\n");
		getSolver()->addTempWatch(p, new PWWatch(this, w.getIndex(), true, false));
		for(int i=0; confl==nullPtrClause && i<watched.size(); i++){
			const Lit& l = watched[i].getLit();
			if(var(l)!=var(p)){
				confl = getSolver()->notifySolver(l, new AggReason(*getAgg()[0], l, BASEDONCC, false));
			}
		}
	}else{
		//gprintLit(~watched[w.getIndex()].getLit()); reportf(" is replaced with "); gprintLit(~rest[ind].getLit()); reportf("\n");
		WL temp = watched[w.getIndex()];
		watched[w.getIndex()] = rest[ind];
		rest[ind] = temp;
		getSolver()->addTempWatch(~watched[w.getIndex()].getLit(), new PWWatch(this, w.getIndex(), true, false));
	}

	return confl;
/*	//find the index
	int index = 0;
	for(int index=0; index<watched.size(); index++){
		if(~l==watched[index]){
			break;
		}
	}
	//find a new one if possible
	pAgg agg = getAgg()[0];
	bool findmon = agg->isMonotone(WLV(l, 1, l_True));
	int swapindex = -1;
	for(int i=0; swapindex==-1 && i<nonwatched.size(); i++){
		if(findmon){
			if(agg->isMonotone(WLV(nonwatched[i], 1, l_Undef)) && getSolver()->value(nonwatched[i])!=l_False){
				swapindex=i;
			}else if(!agg->isMonotone(WLV(nonwatched[i], 1, l_Undef)) && getSolver()->value(nonwatched[i])!=l_True){
				swapindex=i;
			}
		}else{
			if(!agg->isMonotone(WLV(nonwatched[i], 1, l_Undef)) && getSolver()->value(nonwatched[i])!=l_False){
				swapindex=i;
			}else if(agg->isMonotone(WLV(nonwatched[i], 1, l_Undef)) && getSolver()->value(nonwatched[i])!=l_True){
				swapindex=i;
			}
		}
	}
	if(swapindex==-1){
		//no other found, do propagation
		//TODO
	}else{
		Lit temp = watched[index];
		watched[index] = nonwatched[swapindex];
		nonwatched[swapindex] = temp;
	}

	return nullPtrClause;*/
}

rClause CardPWAgg::propagate(const Agg& agg){
	assert(false);
};

void CardPWAgg::backtrack(const Agg& agg){
	assert(false);
}

void CardPWAgg::getExplanation(vec<Lit>& lits, const AggReason& ar) const{
	for(int i=0; i<getWL().size(); i++){
		if(getSolver()->value(getWL()[i].getLit())==l_False){
			lits.push(getWL()[i].getLit());
		}
	}
};

Weight CardPWAgg::getBestPossible() const{
	Weight max = getESV();
	for (vwl::const_iterator j = getWL().begin(); j < getWL().end(); j++) {
		max = this->add(max, (*j).getWeight());
	}
	return max;
}

bool CardPWAgg::canJustifyHead(const Agg& agg, vec<Lit>& jstf, vec<Var>& nonjstf, vec<int>& currentjust, bool real) const{
	AggrType type = agg.getAggComb()->getType();
	bool justified = false;
	const vwl& wl = getWL();

	if(agg.isLower()){
		Weight bestpossible = getBestPossible();
		for (vwl::const_iterator i = wl.begin(); !justified && i < wl.end(); ++i) {
			if(oppositeIsJustified(*i, currentjust, real, getSolver())){
				jstf.push(~(*i).getLit());
				bestpossible = remove(bestpossible, (*i).getWeight());
				if (bestpossible <= agg.getLowerBound()){
					justified = true;
				}
			}else if(real ||currentjust[var((*i).getLit())]!=0){
				nonjstf.push(var((*i).getLit()));
			}
		}
	}else{
		Weight bestcertain = getESV();
		for (vwl::const_iterator i = wl.begin(); !justified && i < wl.end(); ++i) {
			if(isJustified(*i, currentjust, real, getSolver())){
				jstf.push((*i).getLit());
				bestcertain = add(bestcertain, (*i).getWeight());
				if (bestcertain >= agg.getUpperBound()){
					justified = true;
				}
			}else if(real ||currentjust[var((*i).getLit())]!=0){
				nonjstf.push(var((*i).getLit()));
			}
		}
	}

	if(getSolver()->verbosity() >=4){
		reportf("Justification checked for ");
		printAgg(agg);

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

Weight CardPWAgg::getCombinedWeight(const Weight& one, const Weight& two) 	const{
	return one+two;
};

WL CardPWAgg::handleOccurenceOfBothSigns(const WL& one, const WL& two){
	if(one.getWeight()>two.getWeight()){
		setESV(getESV() + two.getWeight());
		return WL(one.getLit(), one.getWeight()-two.getWeight());
	}else{
		setESV(getESV() + one.getWeight());
		return WL(one.getLit(), two.getWeight()-one.getWeight());
	}
};

///////
// DEBUG
///////

void Aggrs::printAgg(AggComb const * const c, bool endl){
	reportf("%s{", c->getName());
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

	if(ae.isLower()){
		reportf(" <- ");
	}else{
		reportf(" <- %s <= ", printWeight(ae.getUpperBound()).c_str());
	}
	printAgg(ae.getAggComb(), false);

	FWAgg const * const s = dynamic_cast<FWAgg*>(ae.getAggComb());
	if(s!=NULL){
		if(ae.isLower()){
			reportf(" <= %s. Known values: bestcertain=%s, bestpossible=%s\n", printWeight(ae.getLowerBound()).c_str(), printWeight(s->getCC()).c_str(), printWeight(s->getCP()).c_str());
		}else{
			reportf(". Known values: bestcertain=%s, bestpossible=%s\n", printWeight(s->getCC()).c_str(), printWeight(s->getCP()).c_str());
		}
	}else{
		if(ae.isLower()){
			reportf(" <= %s.\n", printWeight(ae.getLowerBound()).c_str());
		}else{
			reportf(".\n");
		}
	}

}
