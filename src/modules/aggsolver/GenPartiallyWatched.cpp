#include "modules/aggsolver/PartiallyWatched.hpp"

#include "modules/AggSolver.hpp"
#include "modules/aggsolver/AggPrint.hpp"
#include "theorysolvers/PCSolver.hpp"

#include <stdint.h>
#include <inttypes.h>
#include <limits.h>

using namespace std;
using namespace MinisatID;
using namespace MinisatID::Aggrs;

/*
 * index is the index in the original set, from which it should be removed
 * w indicates the set to which it should be added
 */
void GenPWAgg::addToWatchedSet(vsize index){
	vpgpw& set = getNWS();
	vpgpw& watches = getWS();
	pgpw watch = set[index];
	watches.push_back(watch);
	if(set.size()>1){
		set[index] = set[set.size()-1];
	}
	set.pop_back();

	watch->pushIntoSet(watches.size()-1);
}

/**
 * @pre: one watch should be moved from a watched set to a nonwatched set
 */
void GenPWAgg::removeFromWatchedSet(pgpw pw){
	vpgpw& set = getNWS();
	vpgpw& watches = getWS();

	if(watches.size()>1){
		int index = pw->getIndex();
		watches[index] = watches[watches.size()-1];
		watches[index]->setIndex(index);
	}
	set.push_back(pw);
	watches.pop_back();

	pw->removedFromSet();
}

/*
 * Removes a literal from its set and adds it to a watched set
 */
void GenPWAgg::addWatchToNetwork(pgpw watch){
	if(watch->isWatched() && !watch->isInUse()){
		watch->setInUse(true);
		getSolver()->addTempWatch(watch->getWatchLit(), watch);
	}
}

void GenPWAgg::addWatchesToNetwork(){
	for(vpgpw::const_iterator i=getWS().begin(); i<getWS().end(); i++){
		addWatchToNetwork(*i);
	}
}

/**
 * Set has at least one aggregate
 * All aggregates have the same sign and implication instead of equivalence, head can be negative!
 */
PWAgg::PWAgg				(TypedSet* set): Propagator(set) {}
GenPWAgg::GenPWAgg			(TypedSet* set): PWAgg(set), genmin(Weight(0)), genmax(Weight(0)){}
CardGenPWAgg::CardGenPWAgg	(TypedSet* set):GenPWAgg(set){}
SumGenPWAgg::SumGenPWAgg	(TypedSet* set):GenPWAgg(set){}

GenPWAgg::~GenPWAgg(){
	deleteList<GenPWatch>(ws);
	deleteList<GenPWatch>(nws);
}

/**
 * initialize NWS: make a watch for each set literal, watch the negation of the set literal if its monotone
 *					then reconstruct the set for the aggregate with the lowest bound!
 */
void GenPWAgg::initialize(bool& unsat, bool& sat) {
	TypedSet* setp = getSetp();
	const TypedSet& set = getSet();
	const vwl& wls = set.getWL();
	vpagg& aggs = getSet().getAggNonConst();

	//Calculate min and max values over empty interpretation
	//Create sets and watches, initialize min/max values
	genmin = set.getType().getESV();
	genmax = set.getType().getESV();
	Weight temp(0);
	for(vsize i=0; i<wls.size(); i++){
		const WL& wl = wls[i];
		bool mono = set.getType().isMonotone(*aggs[0], wl);
		nws.push_back(new GenPWatch(setp, wl, mono));
		if(wl.getWeight()<0){
			genmin = set.getType().add(genmin, wl.getWeight());
		}else{
			genmax = set.getType().add(genmax, wl.getWeight());
		}
	}

	//FIXME add propagation HEAD2 => HEAD: VERY USEFUL PROBABLY
	//HEAD <=> agg >= x
	//HEAD2 <=> agg >= x+1

	//Go over aggregates, find lowest bound of both known and unknown agg
	//TODO save them and always use them?
	//TODO sorted aggr? //TODO 2 remember optim!

	//Check for worst aggregate
	bool propagations = false;
	rClause confl = reconstructSet(NULL, propagations);
	if(confl!=nullPtrClause){ unsat = true; sat = false; return; }

	addWatchesToNetwork(); //Add set watches
	PWAgg::initialize(unsat, sat); //Add head watches
}

/**
 * maintaining min/max:
 * init calc: min=getESV, max=getESV
 * init min/max
 * min = sum of all neg weights
 * max = sum of all pos weights
 *
 * mo and true: min+=weight
 * am and true: max+=weight
 * mo and false: max-=weight
 * am and false: min-=weight
 */
//FIXME maximum aggregate
void GenPWAgg::addValue(const Weight& weight, bool inset, Weight& min, Weight& max) const{
	bool pos = weight>=0;
	if(pos && inset){
		min = getSet().getType().add(min, weight);
	}else if(pos && !inset){
		max = getSet().getType().remove(max, weight);
	}else if(!pos && inset){
		max = getSet().getType().add(max, weight);
	}else{ //!pos && !inset
		min = getSet().getType().remove(min, weight);
	}
}

//It was unknown, so inset is true if
void GenPWAgg::removeValue(const Weight& weight, bool inset, Weight& min, Weight& max) const{
	bool pos = weight>=0;
	if(pos && inset){
		min = getSet().getType().remove(min, weight);
	}else if(pos && !inset){
		max = getSet().getType().add(max, weight);
	}else if(!pos && inset){
		max = getSet().getType().remove(max, weight);
	}else{ //!pos && !inset
		min = getSet().getType().add(min, weight);
	}
}

rClause GenPWAgg::checkPropagation(bool& propagations){
	Weight min = genmin;
	Weight max = genmax;

	//FIXME: can remove propagatedvalue everywhere except getexplanation if checking here for unsat also and generate explanation based on last propagation

	for(vpgpw::const_iterator i=getWS().begin(); i<getWS().end(); i++){
		const WL& wl = (*i)->getWL();
		lbool val = propagatedValue(wl.getLit());
		if(val!=l_Undef){
			addValue(wl.getWeight(), val==l_True, min, max);
		}
	}

	for(vpgpw::const_iterator i=getNWS().begin(); i<getNWS().end(); i++){
		const WL& wl = (*i)->getWL();
		lbool val = propagatedValue(wl.getLit());
		if(val!=l_Undef){
			addValue(wl.getWeight(), val==l_True, min, max);
		}
	}

	const Agg& agg = *getSet().getAgg()[0];
	rClause confl = nullPtrClause;
	Expl basedon = agg.hasLB()?BASEDONCP:BASEDONCC;
	if(propagatedValue(agg.getHead())==l_False){
		Weight lowerbound;
		if(agg.hasLB()){
			lowerbound = getSet().getType().remove(max, agg.getCertainBound());
		}else{
			lowerbound = getSet().getType().remove(agg.getCertainBound(), min);
		}
		for(vwl::const_iterator i=getSet().getWL().begin(); confl==nullPtrClause && i<getSet().getWL().end(); i++){
			if((*i).getWeight()>lowerbound && propagatedValue((*i).getLit())==l_Undef){
				propagations = true;
				if (agg.hasLB()) {
					confl = getSet().getSolver()->notifySolver(new AggReason(agg, basedon, (*i).getLit(), (*i).getWeight(), false));
				}else{
					confl = getSet().getSolver()->notifySolver(new AggReason(agg, basedon, ~(*i).getLit(), (*i).getWeight(), false));
				}
			}
		}
	}

	//Check head propagation
	//If agg is true, then propagate ~head (head of THIS aggregate, not the original one)
	//If agg is false, propagate head
	if((agg.hasLB() && agg.getCertainBound()<=min) || (agg.hasUB() && max<=agg.getCertainBound())){
		propagations = true;
		confl = getSet().getSolver()->notifySolver(new AggReason(agg, basedon, ~agg.getHead(), Weight(0), true));
	}else if((agg.hasLB() && max<agg.getCertainBound()) || (agg.hasUB() && agg.getCertainBound()<min)){
		propagations = true;
		confl = getSet().getSolver()->notifySolver(new AggReason(agg, basedon, agg.getHead(), Weight(0), true));
	}

	return confl;
}

/**
 * do propagation, both body and heads:
 * 		calc full min and max
 * reconstruct watches:
 * 		calc min and max of watched set and store largest non-false weight
 * 		keep adding non-false until satisfied
 * 		if head known
 * 			remove largest, keep adding non-false until satisfied
 */
rClause GenPWAgg::reconstructSet(pgpw watch, bool& propagations){
	rClause confl = nullPtrClause;

	lbool headval = propagatedValue(getSet().getAgg()[0]->getHead());
	if(headval==l_True){
		propagations = true;
		return confl;
	}

	confl = checkPropagation(propagations);

	if(confl!=nullPtrClause){
		propagations = true;
		return confl;
	}

	Weight min = genmin, knownmin = genmin;
	Weight max = genmax, knownmax = genmax;
	pgpw largest = NULL;

	bool falsewatches = false;

	//Calc min and max and largest considering optimal choices for the watched literals
	for(vpgpw::const_iterator i=getWS().begin(); i<getWS().end(); i++){
		const WL& wl = (*i)->getWL();
		lbool val = propagatedValue(wl.getLit());
		if(val==l_Undef){ //Only have to check propagation for those watches which are unknown
			if(largest==NULL || largest->getWL().getWeight() < wl.getWeight()){
				largest = (*i);
			}
		}

		bool inset = val==l_True || (val==l_Undef && (*i)->isMonotone());
		addValue(wl.getWeight(), inset, min, max);
		if(val!=l_Undef){
			addValue(wl.getWeight(), val==l_True, knownmin, knownmax);
			if(propagatedValue((*i)->getWatchLit())==l_False){
				falsewatches = true;
			}
		}
	}

	//Add watches until satisfied
	//gprintLit((**getSet().getAgg().begin()).getHead()); report(" %d, %d\n", min, max);
	for(int i=0;
			!isSatisfied(**getSet().getAgg().begin(), min, max) &&
			!isSatisfied(**getSet().getAgg().begin(), knownmin, knownmax) &&
			i<getNWS().size(); i++){
		WL wl = getNWS()[i]->getWL();
		lbool val = propagatedValue(wl.getLit());

		bool inset = val==l_True || (val==l_Undef && getNWS()[i]->isMonotone());
		addValue(wl.getWeight(), inset, min, max);
		if(val!=l_Undef){
			addValue(wl.getWeight(), val==l_True, knownmin, knownmax);
		}

		if(val!=l_False){ //Add to watches
			if(largest==NULL || largest->getWL().getWeight() < wl.getWeight()){
				largest = getNWS()[i];
			}
			addToWatchedSet(i);
			i--;
		}
		//gprintLit((**getSet().getAgg().begin()).getHead()); report(" %d, %d\n", min, max);
	}

	//if head was unknown before method start, at most head can have been propagated
	//so do not have to find second supporting ws
	if(headval==l_Undef){
		return confl;
	}
	//If certainly satisfied, do not have to add more watches
/*	if(isSatisfied(**getSet().getAgg().begin(), knownmin, knownmax)){
		propagations = true;
		return confl;
	}*/
	//TODO previous seems to be an incorrect overapproximation?
	if(largest==NULL){
		propagations = true;
		return confl;
	}


	//Leave out largest and do the same
	assert(largest!=NULL);
	removeValue(largest->getWL().getWeight(), largest->isMonotone(), min, max);

	//Again until satisfied
	for(int i=0;
			!isSatisfied(**getSet().getAgg().begin(), min, max) &&
			!isSatisfied(**getSet().getAgg().begin(), knownmin, knownmax) &&
			i<getNWS().size(); i++){
		WL wl = getNWS()[i]->getWL();
		lbool val = propagatedValue(wl.getLit());

		bool inset = val==l_True || (val==l_Undef && getNWS()[i]->isMonotone());
		addValue(wl.getWeight(), inset, min, max);
		if(val!=l_Undef){
			addValue(wl.getWeight(), val==l_True, knownmin, knownmax);
		}

		if(val!=l_False){ //Add to watches
			if(largest->getWL().getWeight() < wl.getWeight()){
				largest = getNWS()[i];
			}
			addToWatchedSet(i);
			i--;
		}
	}

	if(!isSatisfied(**getSet().getAgg().begin(), min, max)){
		propagations = true;
	}

	return confl;
}

//cannot propagate any heads, so only check body propagation
rClause GenPWAgg::reconstructSet(const Agg& agg, pgpw watch, bool& propagations){
	return reconstructSet(NULL, propagations);
}

rClause GenPWAgg::propagate(const Lit& p, Watch* watch, int level) {
	rClause confl = nullPtrClause;

	GenPWatch* const pw = dynamic_cast<GenPWatch*>(watch);
	assert(pw->isInUse());

	pw->setInUse(false);

	if(!pw->isWatched()){
		assert(pw->getIndex()==-1);
		return confl;
	}

	assert(pw->getIndex()!=-1);

	bool propagations = false;
	confl = reconstructSet(pw, propagations);

	if(!propagations && confl==nullPtrClause){
		removeFromWatchedSet(pw);
	}else{
		addWatchToNetwork(pw);
	}

	addWatchesToNetwork();

	assert(!pw->isWatched() || getWS()[pw->getIndex()]==pw);

	return confl;
}

rClause GenPWAgg::propagate(int level, const Agg& agg, bool headtrue) {
	rClause confl = nullPtrClause;

	bool propagations = false;
	confl = reconstructSet(agg, NULL, propagations);
	addWatchesToNetwork();

	return confl;
}

rClause	GenPWAgg::propagateAtEndOfQueue(int level){
	rClause confl = nullPtrClause;
	return confl;
}

void GenPWAgg::getExplanation(vec<Lit>& lits, const AggReason& ar) {
	const PCSolver& pcsol = *getSolver()->getPCSolver();
	const Lit& head = ar.getAgg().getHead();
	if(propagatedValue(head)!=l_Undef && var(ar.getPropLit())!=var(head)){
		if(pcsol.assertedBefore(var(head), var(ar.getPropLit()))){
			lits.push(propagatedValue(head)==l_True?~head:head);
		}
	}

	Lit comparelit = ar.getPropLit();

	for (vsize i = 0; i < getSet().getWL().size(); i++) {
		const WL& wl = getSet().getWL()[i];
		if (var(wl.getLit()) != var(comparelit) && propagatedValue(wl.getLit()) != l_Undef) {
			if(pcsol.assertedBefore(var(wl.getLit()), var(comparelit))){
				lits.push(propagatedValue(wl.getLit())==l_True?~wl.getLit():wl.getLit());
			}
		}
	}
}
