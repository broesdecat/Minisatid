/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
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
 * TODO sorted aggr? //TODO 2 remember optim!
 * FIXME maximum aggregate
 */

PWAgg::PWAgg				(TypedSet* set): Propagator(set) {}
GenPWAgg::GenPWAgg			(TypedSet* set): PWAgg(set), emptyinterpretbounds(Weight(0), Weight(0)){}
CardGenPWAgg::CardGenPWAgg	(TypedSet* set):GenPWAgg(set){}
SumGenPWAgg::SumGenPWAgg	(TypedSet* set):GenPWAgg(set){}

GenPWAgg::~GenPWAgg(){
	deleteList<GenPWatch>(ws);
	deleteList<GenPWatch>(nws);
}

void GenPWAgg::moveFromNWSToWS(GenPWatch* watch){
	genwatchlist& nonwatched = getNWS();
	genwatchlist& watched = getWS();

	if(nonwatched.size()>1){
		vsize index = watch->getIndex();
		nonwatched[index] = nonwatched[nonwatched.size()-1];
		nonwatched[index]->setIndex(index);
	}
	nonwatched.pop_back();

	watched.push_back(watch);
	watch->moveToWSPos(watched.size()-1);

	getStagedWatches().push_back(watch);

	assert(getNWS().size()+getWS().size()==getSet().getWL().size());
}

void GenPWAgg::moveFromWSToNWS(pgpw pw){
	genwatchlist& nonwatched = getNWS();
	genwatchlist& watched = getWS();

	if(watched.size()>1){
		int index = pw->getIndex();
		watched[index] = watched[watched.size()-1];
		watched[index]->setIndex(index);
	}
	watched.pop_back();

	nonwatched.push_back(pw);
	pw->moveToNWSPos(nonwatched.size()-1);
}

void GenPWAgg::addWatchToNetwork(pgpw watch){
	assert(watch->isInWS());
	if(!watch->isInNetwork()){
		watch->addToNetwork(true);
		getSolver()->addDynamicWatch(watch->getWatchLit(), watch);
	}
}

//In init, not immediately adding watches!
void GenPWAgg::addWatchesToNetwork(){
	for(genwatchlist::const_iterator i=getStagedWatches().begin(); i<getStagedWatches().end(); i++){
		addWatchToNetwork(*i);
	}
	getStagedWatches().clear();
}

/**
 * @pre All aggregates have the same sign and implication instead of equivalence, head can be negative!
 * initialize NWS: make a watch for each set literal, watch the negation of the set literal if its monotone
 *					then reconstruct the set for the aggregate with the lowest bound!
 */
void GenPWAgg::initialize(bool& unsat, bool& sat) {
	TypedSet& set = getSet();
	assert(set.getAgg().size()>0);

#ifdef DEBUG
	const agglist& aggs = set.getAgg();
	AggSign sign = aggs[0]->getSign();
	for(agglist::const_iterator i=aggs.begin(); i<aggs.end(); i++){
		assert((*i)->getSign()==sign);
	}
#endif

	//Initialization
	emptyinterpretbounds = minmaxBounds(set.getType().getMinPossible(set), set.getType().getMaxPossible(set));
	const vwl& wls = set.getWL();
	for(vwl::const_reverse_iterator i=wls.rbegin(); i<wls.rend(); i++){
		const WL& wl = *i;
		bool mono = set.getType().isMonotone(**set.getAgg().begin(), wl.getWeight());
		nws.push_back(new GenPWatch(getSetp(), wl, mono, nws.size()));
	}

	minmaxBounds pessbounds(emptyinterpretbounds);
	for(vsize i=0; i<wls.size(); i++){
		const WL& wl = wls[i];
		lbool val = getSolver()->value(wl.getLit());
		if(val==l_True){
			pessbounds.min = set.getType().add(pessbounds.min, wl.getWeight());
		}else if(val==l_False){
			pessbounds.max = set.getType().remove(pessbounds.max, wl.getWeight());
		}
	}

	//Drop initially sat aggregates and propagate the others
	rClause confl = nullPtrClause;
	agglist rem, del;
	for(agglist::const_iterator i=set.getAgg().begin(); confl==nullPtrClause && i<set.getAgg().end(); i++){
		if(value((*i)->getHead())==l_True && !(*i)->isOptim()){
			del.push_back(*i);
		}else if(isSatisfied(**i, pessbounds) && !(*i)->isOptim()){
			confl = set.getSolver()->notifySolver(new HeadReason(**i, BASEDONCC, ~(*i)->getHead()));
			del.push_back(*i);
		}else if(isFalsified(**i, pessbounds) && !(*i)->isOptim()){
			//propagate head false
			confl = set.getSolver()->notifySolver(new HeadReason(**i, BASEDONCC, (*i)->getHead()));
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
	for(agglist::const_iterator i=set.getAgg().begin(); i<set.getAgg().end(); i++){
		if((*i)->hasLB() && worstagg->getCertainBound()<(*i)->getCertainBound()){
			worstagg = *i;
		}else if((*i)->hasUB() && worstagg->getCertainBound()>(*i)->getCertainBound()){
			worstagg = *i;
		}
	}

	bool propagations = false;
	confl = reconstructSet(NULL, propagations, NULL);
	if(confl!=nullPtrClause){ unsat = true; sat = false; return; }

	addWatchesToNetwork(); //Add set watches
	PWAgg::initialize(unsat, sat); //Add head watches
}

Agg* getAggWithMostStringentBound(const GenPWAgg& prop){
	Agg* strongestagg = NULL;
	for(agglist::const_iterator i=prop.getSet().getAgg().begin(); i<prop.getSet().getAgg().end(); i++){
		bool headfalse = prop.value((*i)->getHead())==l_False;
		if(headfalse){
			if(strongestagg==NULL){
				strongestagg = *i;
			}else if(strongestagg->hasLB() && strongestagg->getCertainBound()<(*i)->getCertainBound()){
				strongestagg = *i;
			}else if(strongestagg->hasUB() && strongestagg->getCertainBound()>(*i)->getCertainBound()){
				strongestagg = *i;
			}
		}
	}
	return strongestagg;
}

//@pre: min and max are the bounds considering the truth! of all known literals
rClause GenPWAgg::checkPropagation(bool& propagations, minmaxBounds& pessbounds, Agg const * aggofprophead){
	rClause confl = nullPtrClause;
	Agg const * aggp = NULL;

	if(aggofprophead!=NULL){
		confl = checkOneAggPropagation(propagations, *aggofprophead, pessbounds);
		aggp = aggofprophead;
	}else{
		for(agglist::const_iterator i=getSet().getAgg().begin(); confl==nullPtrClause && i<getSet().getAgg().end(); i++){
			confl = checkOneAggPropagation(propagations, **i, pessbounds);
		}
		aggp = getAggWithMostStringentBound(*this);
	}

	if(confl==nullPtrClause && aggp!=NULL){
		const Agg& agg = *aggp;
		WL lowerbound(mkLit(1), Weight(0));
		if(agg.hasLB()){
			lowerbound = WL(mkLit(1), getSet().getType().remove(pessbounds.max, agg.getCertainBound()));
		}else{
			lowerbound = WL(mkLit(1), getSet().getType().remove(agg.getCertainBound(), pessbounds.min));
		}
		vwl::const_iterator i = upper_bound(getSet().getWL().begin(), getSet().getWL().end(), lowerbound, compareWLByWeights);
		for(; confl==nullPtrClause && i<getSet().getWL().end(); i++){ //INVARIANT: sorted WL
			if(value((*i).getLit())==l_Undef){
				propagations = true;
				if (agg.hasLB()) {
					confl = getSolver()->notifySolver(new SetLitReason(agg, (*i).getLit(), (*i).getWeight(), agg.hasLB()?BASEDONCP:BASEDONCC, true));
				}else{
					confl = getSolver()->notifySolver(new SetLitReason(agg, (*i).getLit(), (*i).getWeight(), agg.hasLB()?BASEDONCP:BASEDONCC, false));
				}
			}
		}
	}

	return confl;
}

rClause GenPWAgg::checkOneAggPropagation(bool& propagations, const Agg& agg, const minmaxBounds& pessbounds){
	rClause confl = nullPtrClause;
	Expl basedon = agg.hasLB()?BASEDONCP:BASEDONCC;

	//Check head propagation
	//If agg is false, propagate head
	if((agg.hasLB() && pessbounds.max<agg.getCertainBound()) || (agg.hasUB() && agg.getCertainBound()<pessbounds.min)){
		propagations = true;
		confl = getSolver()->notifySolver(new HeadReason(agg, basedon, agg.getHead()));
	}
	return confl;
}

void GenPWAgg::calculateBoundsOfWatches(minmaxOptimAndPessBounds& bounds, GenPWatch*& largest){
	//Calc min and max and largest considering optimal choices for the watched literals
	for(genwatchlist::const_iterator i=getWS().begin(); i<getWS().end(); i++){
		const WL& wl = (*i)->getWL();
		lbool val = value(wl.getLit());
		if(val==l_Undef){ //Only have to check propagation for those watches which are unknown
			if(largest==NULL || largest->getWL().getWeight() < wl.getWeight()){
				largest = (*i);
			}
		}

		bool inset = val==l_True || (val==l_Undef && (*i)->isMonotone());
		addValue(getSet().getType(), wl.getWeight(), inset, bounds.optim);
		if(val!=l_Undef){
			addValue(getSet().getType(), wl.getWeight(), val==l_True, bounds.pess);
		}
	}
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
#ifdef DEBUG
	for(vwl::const_iterator i=getSet().getWL().begin(); i<getSet().getWL().end(); i++){
		bool found = false;
		for(genwatchlist::const_iterator j=getNWS().begin(); j<getNWS().end(); j++){
			if(var((*i).getLit())==var((*j)->getWL().getLit())){
				found = true;
			}
		}
		for(genwatchlist::const_iterator j=getWS().begin(); j<getWS().end(); j++){
			if(var((*i).getLit())==var((*j)->getWL().getLit())){
				found = true;
			}
		}
		assert(found);
	}
#endif

	rClause confl = nullPtrClause;

	bool oneagg = getSet().getAgg().size()==1;
	const Agg& agg = *getWorstAgg();

	//possible HACK: watch all at all times
	/*for(int i=0 ;i<getNWS().size(); i++){
		addToWatchedSet(i);
		i--;
	}*/

	//possible HACK: always keep watch
	//propagations = true;

	if(oneagg && value(agg.getHead())==l_True){
		propagations = true;
		return confl;
	}

	minmaxOptimAndPessBounds bounds(getEmptyInterpretationBounds());
	pgpw largest = NULL;

	calculateBoundsOfWatches(bounds, largest);

	//Add watches until satisfied
	vsize i = 0;
	vector<GenPWatch*> watchestoadd;
	genWatches(i, agg, bounds, largest, watchestoadd);
	if(!isSatisfied(agg, bounds.optim)){
		//Certainly head propagation, no more watches to be found or added
		return checkPropagation(propagations, bounds.pess, propagg);
	}else{
		for(vector<GenPWatch*>::const_iterator i=watchestoadd.begin(); i<watchestoadd.end(); i++){
			moveFromNWSToWS(*i);
		}
		watchestoadd.clear();
	}

	//if head was unknown before method start, at most head can have been propagated
	//so do not have to find second supporting ws
	if(oneagg && value(agg.getHead())==l_Undef){
		return confl;
	}
	//If certainly satisfied, do not have to add more watches, but do not delete the current ones!
	if(largest==NULL || isSatisfied(agg, bounds.pess)){
		propagations = true;
		return confl;
	}

	//Leave out largest and do the same
	assert(largest!=NULL);
	removeValue(getSet().getType(), largest->getWL().getWeight(), largest->isMonotone(), bounds.optim);

	//Again until satisfied IMPORTANT: continue from previous index!
	genWatches(i, agg, bounds, largest, watchestoadd);
	if(!isSatisfied(agg, bounds.optim)){
		watchestoadd.clear();
		confl = checkPropagation(propagations, bounds.pess, propagg);
		if(confl!=nullPtrClause){
			propagations = true;
			return confl;
		}
		genWatches(i, agg, bounds, largest, watchestoadd);
	}
	for(vector<GenPWatch*>::const_iterator i=watchestoadd.begin(); i<watchestoadd.end(); i++){
		moveFromNWSToWS(*i);
	}
	watchestoadd.clear();

#ifdef DEBUG
	for(vwl::const_iterator i=getSet().getWL().begin(); i<getSet().getWL().end(); i++){
		bool found = false;
		for(genwatchlist::const_iterator j=getNWS().begin(); j<getNWS().end(); j++){
			if(var((*i).getLit())==var((*j)->getWL().getLit())){
				found = true;
			}
		}
		for(genwatchlist::const_iterator j=getWS().begin(); j<getWS().end(); j++){
			if(var((*i).getLit())==var((*j)->getWL().getLit())){
				found = true;
			}
		}
		assert(found);
	}
#endif

	return confl;
}

void GenPWAgg::genWatches(vsize& i, const Agg& agg, minmaxOptimAndPessBounds& bounds, GenPWatch*& largest, vector<GenPWatch*>& watchestoadd){
	for(;!isSatisfied(agg, bounds.optim) && !isSatisfied(agg, bounds.pess) && i<getNWS().size(); i++){
		GenPWatch* watch = getNWS()[i];
		WL wl = watch->getWL();
		lbool val = value(wl.getLit());

		bool inset = val==l_True || (val==l_Undef && watch->isMonotone());
		addValue(getSet().getType(), wl.getWeight(), inset, bounds.optim);
		if(val!=l_Undef){
			addValue(getSet().getType(), wl.getWeight(), val==l_True, bounds.pess);
		}

		if((watch->isMonotone() && val!=l_False) || (!watch->isMonotone() && val!=l_True)){
			if(largest==NULL || largest->getWL().getWeight() < wl.getWeight()){
				largest = watch;
			}
			moveFromNWSToWS(watch);
			i--;
		}
	}
	assert(!isSatisfied(agg, bounds.pess) || isSatisfied(agg, bounds.optim));
	assert(isSatisfied(agg, bounds.optim) || i>=getNWS().size());
}

rClause GenPWAgg::propagate(const Lit& p, Watch* watch, int level) {
	rClause confl = nullPtrClause;

	GenPWatch* const pw = dynamic_cast<GenPWatch*>(watch);

	//Watch has to be in network to cause propagation. Before calling this method, it is removed from the network, so
	//we also remove it here
	assert(pw->isInNetwork());
	pw->addToNetwork(false);

	if(!pw->isInWS()){ //If the watch is in NWS, it should not have been watched any more, so we can just return
		assert(getNWS()[pw->getIndex()]==pw); //Check it has a correct idea where it is in WS
		return confl;
	}

	assert(getWS()[pw->getIndex()]==pw); //Check it has a correct idea where it is in WS

	bool propagations = false;
	confl = reconstructSet(pw, propagations, NULL);

	if(!propagations && confl==nullPtrClause){ //It can be safely removed as a watch, so we also remove it from WS
		moveFromWSToNWS(pw);
	}else{ //Otherwise, we add it again to the network
		addWatchToNetwork(pw);
	}

	addWatchesToNetwork();

	assert(!pw->isInWS() || getWS()[pw->getIndex()]==pw);
	return confl;
}

rClause GenPWAgg::propagate(int level, const Agg& agg, bool headtrue) {
	bool propagations = false;
	rClause confl = reconstructSet(NULL, propagations, &agg);
	addWatchesToNetwork();
	return confl;
}

/**
 * NOOP, all propagation is done in propagate
 */
rClause	GenPWAgg::propagateAtEndOfQueue(int level){
	rClause confl = nullPtrClause;
	return confl;
}

struct WLI: public WL{
	int time;
	bool inset;

	WLI(): WL(createPositiveLiteral(1), Weight(0)), time(0), inset(false){}
	WLI(const WL& wl, int time, bool inset): WL(wl), time(time), inset(inset){}
};

bool compareWLIearlier(const WLI& one, const WLI& two){
	return one.time < two.time;
}

void GenPWAgg::getExplanation(vec<Lit>& lits, const AggReason& ar) {
	const PCSolver& pcsol = getSolver()->getPCSolver();

	const Lit& head = ar.getAgg().getHead();
	const Lit& proplit = ar.getPropLit();
	bool conflictclause = value(ar.getPropLit())==l_False;
	lbool headval = value(head);
	//if head known and not propagated and generating conflict clause or asserted before
	if(headval!=l_Undef && var(ar.getPropLit())!=var(head) &&
			(conflictclause || pcsol.assertedBefore(var(head), var(proplit)))){
		lits.push(headval==l_True?~head:head);
	}

	vector<WLI> wlis;
	for(genwatchlist::const_iterator i=getWS().begin(); i<getWS().end(); i++){
		if(var((*i)->getWatchLit())!=var(proplit)){
			lbool val = value((*i)->getWatchLit());
			if(val==l_True){
				wlis.push_back(WLI((*i)->getWL(), getSolver()->getTime((*i)->getWL().getLit()), (*i)->getWatchLit()==(*i)->getWL().getLit()));
			}
		}
	}
	for(genwatchlist::const_iterator i=getNWS().begin(); i<getNWS().end(); i++){
		if(var((*i)->getWatchLit())!=var(proplit)){
			lbool val = value((*i)->getWatchLit());
			if(val==l_True){
				wlis.push_back(WLI((*i)->getWL(), getSolver()->getTime((*i)->getWL().getLit()), (*i)->getWatchLit()==(*i)->getWL().getLit()));
			}
		}
	}

	//Follow propagation order
	sort(wlis.begin(), wlis.end(), compareWLIearlier);

	minmaxBounds pessbounds(getEmptyInterpretationBounds());
	if(!ar.isHeadReason()){ //Change value according to propagating negation of proplit
		addValue(getSet().getType(), ar.getPropWeight(), !ar.isInSet(), pessbounds);
	}

	//Calc min and max
	for(vector<WLI>::const_iterator i=wlis.begin(); !isFalsified(ar.getAgg(), pessbounds) && i<wlis.end(); i++){
		const WLI& wl = *i;
		if(var(wl.getLit())==var(proplit)){
			continue;
		}
		lbool val = value(wl.getLit());

		if(conflictclause || pcsol.assertedBefore(var(wl.getLit()), var(proplit))){
			addValue(getSet().getType(), wl.getWeight(), wl.inset, pessbounds); //TODO addvalue was incorectly out of the if, but none of the fast tests detected this!
			lits.push(val==l_True?~wl.getLit():wl.getLit());
		}
	}
	assert(isFalsified(ar.getAgg(), pessbounds));
}

double GenPWAgg::testGenWatchCount() {
	TypedSet& set = getSet();

	//Calculate min and max values over empty interpretation
	//Create sets and watches, initialize min/max values
	emptyinterpretbounds = minmaxBounds(set.getType().getMinPossible(set), set.getType().getMaxPossible(set));
	const vwl& wls = set.getWL();
	for(vsize i=0; i<wls.size(); i++){
		const WL& wl = wls[i];
		bool mono = set.getType().isMonotone(**set.getAgg().begin(), wl.getWeight());
		nws.push_back(new GenPWatch(getSetp(), wl, mono, nws.size()));
	}

	//Calculate reference aggregate (the one which will lead to the most watches
	worstagg = *set.getAgg().begin();
	for(agglist::const_iterator i=set.getAgg().begin(); i<set.getAgg().end(); i++){
		if((*i)->hasLB() && worstagg->getCertainBound()<(*i)->getCertainBound()){
			worstagg = *i;
		}else if((*i)->hasUB() && worstagg->getCertainBound()>(*i)->getCertainBound()){
			worstagg = *i;
		}
	}

	bool oneagg = getSet().getAgg().size()==1;
	const Agg& agg = *worstagg;

	if(oneagg && value(agg.getHead())==l_True){
		return 0;
	}

	minmaxOptimAndPessBounds bounds(emptyinterpretbounds);
	pgpw largest = NULL;

	bool falsewatches = false;

	//Calc min and max and largest considering optimal choices for the watched literals
	for(genwatchlist::const_iterator i=getWS().begin(); i<getWS().end(); i++){
		const WL& wl = (*i)->getWL();
		lbool val = value(wl.getLit());
		if(val==l_Undef){ //Only have to check propagation for those watches which are unknown
			if(largest==NULL || largest->getWL().getWeight() < wl.getWeight()){
				largest = (*i);
			}
		}

		bool inset = val==l_True || (val==l_Undef && (*i)->isMonotone());
		addValue(getSet().getType(), wl.getWeight(), inset, bounds.optim);
		if(val!=l_Undef){
			addValue(getSet().getType(), wl.getWeight(), val==l_True, bounds.pess);
			if(value((*i)->getWatchLit())==l_False){
				falsewatches = true;
			}
		}
	}

	vsize i = 0;
	for(;!isSatisfied(agg, bounds.optim) && !isSatisfied(agg, bounds.pess) && i<getNWS().size(); i++){
		WL wl = getNWS()[i]->getWL();
		lbool val = value(wl.getLit());

		bool inset = val==l_True || (val==l_Undef && getNWS()[i]->isMonotone());
		addValue(getSet().getType(), wl.getWeight(), inset, bounds.optim);
		if(val!=l_Undef){
			addValue(getSet().getType(), wl.getWeight(), val==l_True, bounds.pess);
		}

		if(val!=l_False){ //Add to watches
			if(largest==NULL || largest->getWL().getWeight() < wl.getWeight()){
				largest = getNWS()[i];
			}
			moveFromNWSToWS(getNWS()[i]);
			i--;
		}
	}

	//if head was unknown before method start, at most head can have been propagated
	//so do not have to find second supporting ws
	if((!oneagg || value(agg.getHead())!=l_Undef) && (largest!=NULL && !isSatisfied(agg, bounds.pess))){
		removeValue(getSet().getType(), largest->getWL().getWeight(), largest->isMonotone(), bounds.optim);

		//Again until satisfied IMPORTANT: continue from previous index!
		for(; !isSatisfied(agg, bounds.optim) && !isSatisfied(agg, bounds.pess) && i<getNWS().size(); i++){
			WL wl = getNWS()[i]->getWL();
			lbool val = value(wl.getLit());

			bool inset = val==l_True || (val==l_Undef && getNWS()[i]->isMonotone());
			addValue(getSet().getType(), wl.getWeight(), inset, bounds.optim);
			if(val!=l_Undef){
				addValue(getSet().getType(), wl.getWeight(), val==l_True, bounds.pess);
			}

			if(val!=l_False){ //Add to watches
				if(largest->getWL().getWeight() < wl.getWeight()){
					largest = getNWS()[i];
				}
				moveFromNWSToWS(getNWS()[i]);
				i--;
			}
		}
	}

	double ratio = ((double)ws.size())/(ws.size()+nws.size());
	Print::printSetWatchRatio(clog, getSet().getSetID(), ratio, getSolver()->verbosity());
	return ratio;
}
