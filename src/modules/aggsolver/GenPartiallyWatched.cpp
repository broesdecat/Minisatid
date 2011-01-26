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

/**
 * TODO: method to test-generate the watches without side effects (const), so a heuristic can be made on the number of watches
 * TODO explanation that searches until satisfied
 * 		beste implementatie: propagatedvalue houdt niet alleen een literal maar ook een volgnummer bij (gemakkelijk want is voor alle literals)
 * 		op die manier heel makkelijk checken of propagatedbefore
 *
 * 		voor until-satisfied, code gebruiken uit reconstructset
 * TODO do not go over all aggregates if one head was propagated
 * TODO sorted aggr? //TODO 2 remember optim!
 * FIXME maximum aggregate
 */

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
	TypedSet& set = getSet();

	assert(set.getAgg().size()>0);

#ifdef DEBUG
	const vpagg& aggs = set.getAgg();
	AggSign sign = aggs[0]->getSign();
	for(auto i=aggs.begin(); i<aggs.end(); i++){
		assert((*i)->getSign()==sign);
	}
#endif

	//Calculate min and max values over empty interpretation
	//Create sets and watches, initialize min/max values
	genmin = set.getType().getESV();
	genmax = set.getType().getESV();
	const vwl& wls = set.getWL();
	Weight temp(0);
	for(vsize i=0; i<wls.size(); i++){
		const WL& wl = wls[i];
		bool mono = set.getType().isMonotone(**set.getAgg().begin(), wl);
		nws.push_back(new GenPWatch(getSetp(), wl, mono));
		if(wl.getWeight()<0){
			genmin = set.getType().add(genmin, wl.getWeight());
		}else{
			genmax = set.getType().add(genmax, wl.getWeight());
		}
	}

	//Drop initially sat aggregates and propagate the others
	rClause confl = nullPtrClause;
	vpagg rem, del;
	for(auto i=set.getAgg().begin(); confl==nullPtrClause && i<set.getAgg().end(); i++){
		if(value((*i)->getHead())==l_True){ //noop
			del.push_back(*i);
		}else if(isSatisfied(**i, genmin, genmax)){
			//propagate head
			confl = set.getSolver()->notifySolver(new AggReason(**i, BASEDONCC, ~(*i)->getHead(), Weight(0), true));
			del.push_back(*i);
		}else{
			rem.push_back(*i);
		}
	}
	set.replaceAgg(rem, del);
	if(confl!=nullPtrClause){
		unsat = true; return;
	}else if(set.getAgg().size()==0){
		sat = true; return;
	}

	//Calculate reference aggregate (the one which will lead to the most watches
	worstagg = *set.getAgg().begin();
	for(auto i=set.getAgg().begin(); i<set.getAgg().end(); i++){
		if((*i)->hasLB() && worstagg->getCertainBound()<(*i)->getCertainBound()){
			worstagg = *i;
		}else if((*i)->hasUB() && worstagg->getCertainBound()<(*i)->getCertainBound()){
			worstagg = *i;
		}
	}

	bool propagations = false;
	confl = reconstructSet(NULL, propagations, NULL);
	if(confl!=nullPtrClause){ unsat = true; sat = false; return; }

	addWatchesToNetwork(); //Add set watches
	PWAgg::initialize(unsat, sat); //Add head watches

	if(getSolver()->verbosity()>=1){
		report("> Set %d: watch ratio of %f\n", getSet().getSetID(), ((double)getWS().size())/(getWS().size()+getNWS().size()));
	}
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

rClause GenPWAgg::checkPropagation(bool& propagations, Agg const * agg){
	Weight min = genmin;
	Weight max = genmax;

	for(vpgpw::const_iterator i=getWS().begin(); i<getWS().end(); i++){
		const WL& wl = (*i)->getWL();
		lbool val = value(wl.getLit());
		if(val!=l_Undef){
			addValue(wl.getWeight(), val==l_True, min, max);
		}
	}

	for(vpgpw::const_iterator i=getNWS().begin(); i<getNWS().end(); i++){
		const WL& wl = (*i)->getWL();
		lbool val = value(wl.getLit());
		if(val!=l_Undef){
			addValue(wl.getWeight(), val==l_True, min, max);
		}
	}

	rClause confl = nullPtrClause;
	if(agg!=NULL){
		confl = checkOneAggPropagation(propagations, *agg, min, max);
	}else{
		for(auto i=getSet().getAgg().begin(); confl==nullPtrClause && i<getSet().getAgg().end(); i++){
			confl = checkOneAggPropagation(propagations, **i, min, max);
		}
	}

	return confl;
}

rClause GenPWAgg::checkOneAggPropagation(bool& propagations, const Agg& agg, const Weight& min, const Weight& max){
	rClause confl = nullPtrClause;
	Expl basedon = agg.hasLB()?BASEDONCP:BASEDONCC;
	if(value(agg.getHead())==l_False){
		Weight lowerbound;
		if(agg.hasLB()){
			lowerbound = getSet().getType().remove(max, agg.getCertainBound());
		}else{
			lowerbound = getSet().getType().remove(agg.getCertainBound(), min);
		}
		for(vwl::const_iterator i=getSet().getWL().begin(); confl==nullPtrClause && i<getSet().getWL().end(); i++){
			if((*i).getWeight()>lowerbound && value((*i).getLit())==l_Undef){
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
	//If agg is false, propagate head
	if((agg.hasLB() && max<agg.getCertainBound()) || (agg.hasUB() && agg.getCertainBound()<min)){
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
rClause GenPWAgg::reconstructSet(pgpw watch, bool& propagations, Agg const * propagg){
	rClause confl = nullPtrClause;

	bool oneagg = getSet().getAgg().size()==1;
	const Agg& agg = *worstagg;

	if(oneagg && value(agg.getHead())==l_True){
		propagations = true;
		return confl;
	}

	confl = checkPropagation(propagations, propagg);

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
		lbool val = value(wl.getLit());
		if(val==l_Undef){ //Only have to check propagation for those watches which are unknown
			if(largest==NULL || largest->getWL().getWeight() < wl.getWeight()){
				largest = (*i);
			}
		}

		bool inset = val==l_True || (val==l_Undef && (*i)->isMonotone());
		addValue(wl.getWeight(), inset, min, max);
		if(val!=l_Undef){
			addValue(wl.getWeight(), val==l_True, knownmin, knownmax);
			if(value((*i)->getWatchLit())==l_False){
				falsewatches = true;
			}
		}
	}

	//Add watches until satisfied
	int i = 0;
	genWatches(i, agg, min, max, knownmin, knownmax, largest);

	//if head was unknown before method start, at most head can have been propagated
	//so do not have to find second supporting ws
	if(oneagg && value(agg.getHead())==l_Undef){
		return confl;
	}
	//If certainly satisfied, do not have to add more watches, but do not delete the current ones!
	if(largest==NULL || isSatisfied(agg, knownmin, knownmax)){
		propagations = true;
		return confl;
	}

	//Leave out largest and do the same
	assert(largest!=NULL);
	removeValue(largest->getWL().getWeight(), largest->isMonotone(), min, max);

	//Again until satisfied IMPORTANT: continue from previous index!
	genWatches(i, agg, min, max, knownmin, knownmax, largest);

	return confl;
}

void GenPWAgg::genWatches(int& i, const Agg& agg, Weight& min, Weight& max, Weight& knownmin, Weight& knownmax, GenPWatch*& largest){
	for(;!isSatisfied(agg, min, max) && !isSatisfied(agg, knownmin, knownmax) && i<getNWS().size(); i++){
		WL wl = getNWS()[i]->getWL();
		lbool val = value(wl.getLit());

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
	}
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
	confl = reconstructSet(pw, propagations, NULL);

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
	confl = reconstructSet(NULL, propagations, &agg);
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
	const Lit& comparelit = ar.getPropLit();
	bool conflictclause = value(ar.getPropLit())==l_False;
	lbool headval = value(head);
	//if head known and not propagated and generating conflict clause or asserted before
	if(headval!=l_Undef && var(ar.getPropLit())!=var(head) &&
			(conflictclause || pcsol.assertedBefore(var(head), var(comparelit)))){
		lits.push(headval==l_True?~head:head);
	}

	for (vsize i = 0; i < getSet().getWL().size(); i++) {
		const WL& wl = getSet().getWL()[i];
		lbool val = value(wl.getLit());
		if(var(wl.getLit())!=var(comparelit) && val!=l_Undef &&
				(conflictclause || pcsol.assertedBefore(var(wl.getLit()), var(comparelit)))){
			lits.push(val==l_True?~wl.getLit():wl.getLit());
		}
	}

	if(getSolver()->verbosity()>=5){
		report("Explanation for deriving "); gprintLit(ar.getPropLit());
		report(" in expression ");
		print(getSolver()->verbosity(), ar.getAgg(), false);
		report(" is ");
		for(int i=0; i<lits.size(); i++){
			report(" "); gprintLit(lits[i]);
		}
		report("\n");
	}
}

double GenPWAgg::testGenWatchCount() {
	TypedSet& set = getSet();

	//Calculate min and max values over empty interpretation
	//Create sets and watches, initialize min/max values
	genmin = set.getType().getESV();
	genmax = set.getType().getESV();
	const vwl& wls = set.getWL();
	Weight temp(0);
	for(vsize i=0; i<wls.size(); i++){
		const WL& wl = wls[i];
		bool mono = set.getType().isMonotone(**set.getAgg().begin(), wl);
		nws.push_back(new GenPWatch(getSetp(), wl, mono));
		if(wl.getWeight()<0){
			genmin = set.getType().add(genmin, wl.getWeight());
		}else{
			genmax = set.getType().add(genmax, wl.getWeight());
		}
	}

	//Calculate reference aggregate (the one which will lead to the most watches
	worstagg = *set.getAgg().begin();
	for(auto i=set.getAgg().begin(); i<set.getAgg().end(); i++){
		if((*i)->hasLB() && worstagg->getCertainBound()<(*i)->getCertainBound()){
			worstagg = *i;
		}else if((*i)->hasUB() && worstagg->getCertainBound()<(*i)->getCertainBound()){
			worstagg = *i;
		}
	}

	bool oneagg = getSet().getAgg().size()==1;
	const Agg& agg = *worstagg;

	if(oneagg && value(agg.getHead())==l_True){
		return 0;
	}

	Weight min = genmin, knownmin = genmin;
	Weight max = genmax, knownmax = genmax;
	pgpw largest = NULL;

	bool falsewatches = false;

	//Calc min and max and largest considering optimal choices for the watched literals
	for(vpgpw::const_iterator i=getWS().begin(); i<getWS().end(); i++){
		const WL& wl = (*i)->getWL();
		lbool val = value(wl.getLit());
		if(val==l_Undef){ //Only have to check propagation for those watches which are unknown
			if(largest==NULL || largest->getWL().getWeight() < wl.getWeight()){
				largest = (*i);
			}
		}

		bool inset = val==l_True || (val==l_Undef && (*i)->isMonotone());
		addValue(wl.getWeight(), inset, min, max);
		if(val!=l_Undef){
			addValue(wl.getWeight(), val==l_True, knownmin, knownmax);
			if(value((*i)->getWatchLit())==l_False){
				falsewatches = true;
			}
		}
	}

	int i = 0;
	for(;!isSatisfied(agg, min, max) && !isSatisfied(agg, knownmin, knownmax) && i<getNWS().size(); i++){
		WL wl = getNWS()[i]->getWL();
		lbool val = value(wl.getLit());

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
	}

	//if head was unknown before method start, at most head can have been propagated
	//so do not have to find second supporting ws
	if(!oneagg || value(agg.getHead())!=l_Undef || (largest!=NULL && !isSatisfied(agg, knownmin, knownmax))){
		removeValue(largest->getWL().getWeight(), largest->isMonotone(), min, max);

		//Again until satisfied IMPORTANT: continue from previous index!
		for(; !isSatisfied(agg, min, max) &&	!isSatisfied(agg, knownmin, knownmax) && i<getNWS().size(); i++){
			WL wl = getNWS()[i]->getWL();
			lbool val = value(wl.getLit());

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
	}

	return ((double)ws.size())/(ws.size()+nws.size());
}
