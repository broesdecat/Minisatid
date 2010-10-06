/*
 * PartiallyWatched.cpp
 *
 *  Created on: Sep 14, 2010
 *      Author: broes
 */

#include "solvers/aggsolver/PartiallyWatched.hpp"

#include "solvers/aggsolver/FullyWatched.hpp"

#include "solvers/aggsolver/AggSolver.hpp"
#include "solvers/pcsolver/PCSolver.hpp"

#include <stdint.h>
#include <inttypes.h>
#include <limits.h>

///////
//PW as().getAgg
///////

inline vpgpw& GenPWAgg::getSet(watchset w) {
	switch (w) {
	case NF:
		return setf;
		break;
	case NT:
		return sett;
		break;
	case NFEX:
		return setf;
		break;
	case NTEX:
		return sett;
		break;
	default:
		assert(false);
		exit(-1);
	}
}

inline vpgpw& GenPWAgg::getWatches(watchset w) {
	switch (w) {
	case NF:
		return nf;
		break;
	case NT:
		return nt;
		break;
	case NFEX:
		return nfex;
		break;
	case NTEX:
		return ntex;
		break;
	default:
		assert(false);
		exit(-1);
	}
}

inline bool GenPWAgg::checking(watchset w) const{
/*	lbool headvalue = propagatedValue(heads[i]);
	switch (w) {
	case NF:
		return headvalue!=l_False;
		break;
	case NT:
		return headvalue!=l_True;
		break;
	case NFEX:
		return headvalue==l_True;
		break;
	case NTEX:
		return headvalue==l_False;
		break;
	default:
		assert(false);
		exit(-1);
	}*/
}


/*
 * index is the index in the original set, from which it should be removed
 * w indicates the set to which it should be added
 */
void GenPWAgg::addToWatchedSet(watchset w, vsize index){
	vpgpw& set = getSet(w);
	vpgpw& watches = getWatches(w);
	pgpw watch = set[index];
	watches.push_back(watch);
	set[index] = set[set.size()-1];
	set.pop_back();

	watch->pushIntoSet(w, watches.size()-1);
}

void GenPWAgg::removeWatchFromSet(watchset w){
	vpgpw& set = getSet(w);
	vpgpw& watches = getWatches(w);

	for(vpgpw::const_iterator i=watches.begin(); i<watches.end(); i++){
		//TODO origineel stond hier ook nog dat inuse false werd gezet, maar mag dit wel?
		(*i)->removedFromSet();
		set.push_back(*(i));
	}
	watches.clear();
}

void GenPWAgg::addWatchesToNetwork(watchset w){
	for(vpgpw::const_iterator i=getWatches(w).begin(); i<getWatches(w).end(); i++){
		addWatchToNetwork(w, *i);
	}
}

/*
 * Removes a literal from its set and adds it to a watched set
 */
void GenPWAgg::addWatchToNetwork(watchset w, pgpw watch){
	watch->setInUse(true);
	as().getSolver()->addTempWatch(watch->getWatchLit(), watch);
}


GenPWAgg::GenPWAgg(paggs agg): PWAgg(agg){
}

GenPWAgg::~GenPWAgg(){
	//TODO delete lists
}

void GenPWAgg::initialize(bool& unsat, bool& sat) {
	vpagg& aggs = as().getRefAgg();
	assert(aggs>0);

	//Verify all aggregates have the same sign:
/*	sign = aggs[0]->getSign();
	for(int i=1; i<aggs.size(); i++){
		if(sign!=aggs[i]->getSign()){
			throw idpexception("The aggregates added to genpwagg do not consistenly have the same type!\n");
		}
	}*/

	const Agg& agg = *aggs[0];

	//Create sets and watches, initialize min/max values
	for(vsize i=0; i<as().getWL().size(); i++){
		const WL& wl = as().getWL()[i];
		if(as().isMonotone(agg, wl)){
			setf.push_back(new GenPWatch(asp(), wl, true, true));
			sett.push_back(new GenPWatch(asp(), wl, false, true));
		}else{
			setf.push_back(new GenPWatch(asp(), wl, false, false));
			sett.push_back(new GenPWatch(asp(), wl, true, false));
		}
	}

	//Initialize NF and NT (all literals are still false!)

	bool nffailed = false, ntfailed = false;
	nffailed = !initialize(agg, NF);
	ntfailed = !initialize(agg, NT);

	rClause confl = nullPtrClause;
	if (nffailed) { //Aggregate is certainly false
		confl = as().getSolver()->notifySolver(new AggReason(agg, mkLit(-1), BASEDONCC, ~agg.getHead(), false));
	}
	if (ntfailed) {
		confl = as().getSolver()->notifySolver(new AggReason(agg, mkLit(-1), BASEDONCP, agg.getHead(), false));
	}
	if(nffailed || ntfailed){
		if(confl!=nullPtrClause){
			unsat = true; sat = false;
			return;
		}else{
			unsat = false; sat = true;
			return;
		}
	}

	//IMPORTANT: only add watches AFTER initialization, otherwise delete is not complete!
	addWatchesToNetwork(NF);
	addWatchesToNetwork(NT);

	PWAgg::initialize(unsat, sat);
}

lbool GenPWAgg::isKnown(const Agg& agg, const vpgpw& set){
	Weight min = as().getESV();
	Weight max = as().getESV();
	for(vpgpw::const_iterator i=set.begin(); i<set.end(); i++){
		const WL& wl = (*i)->getWL();
		if(propagatedValue(wl)==l_True){ //It is in the set
			min=add(min, wl);
			max=add(max, wl);
		}else if(propagatedValue(wl)==l_Undef){ //It might be in the set
			if((*i)->getPos()==POSINSET){
				min=add(min, wl);
				max=add(max, wl);
			}else if((*i)->getPos()==POSSETUNKN){
				if(!(*i)->isMonotone()){
					min = add(min, wl);
				}else{
					max = add(max, wl);
				}
			}
		} //not in the set does not have to be treated!
	}
	if(isSatisfied(agg, min)){
		return l_True;
	}else if(!isSatisfied(agg, max)){
		return l_False;
	}else{
		return l_Undef;
	}
}

bool GenPWAgg::initialize(const Agg& agg, watchset w) {
	vpgpw& set = getSet(w);
	vpgpw& watches = getWatches(w);

	lbool until = isF(w)?l_True:l_False;

	vpgpw ss;
	ss.insert(ss.begin(), set.begin(), set.end());
	ss.insert(ss.begin(), watches.begin(), watches.end());
	for(vsize i=0; isKnown(agg, ss)!=until && i<set.size();){
		if(((isF(w) && set[i]->isMonotone()) || (!isF(w) && !set[i]->isMonotone())) && propagatedValue(set[i]->getWL())!=l_False){
			addToWatchedSet(w, i);
			set[i]->setPos(POSINSET);

		}else if(((isF(w) && !set[i]->isMonotone()) || (!isF(w) && set[i]->isMonotone())) && propagatedValue(set[i]->getWL())!=l_True){
			addToWatchedSet(w, i);
			set[i]->setPos(POSOUTSET);
		}else{
			i++;
		}
		ss.clear();
		ss.insert(ss.begin(), set.begin(), set.end());
		ss.insert(ss.begin(), watches.begin(), watches.end());
	}
	return isKnown(agg, ss)==until;
}

bool GenPWAgg::initializeEX(const Agg& agg, watchset w) {
	bool found = false;
	return found;
}

bool GenPWAgg::replace(vsize index, watchset w) {
	bool found = false;
	return found;
}

rClause GenPWAgg::propagate(const Lit& p, Watch* watch) {
	rClause confl = nullPtrClause;
	return confl;
}

rClause GenPWAgg::propagate(const Agg& agg) {
	rClause confl = nullPtrClause;
	return confl;
}

void GenPWAgg::backtrack(const Agg& agg) {

}

bool GenPWAgg::assertedBefore(const Var& l, const Var& p) const {
	return false;
}

void GenPWAgg::getExplanation(vec<Lit>& lits, const AggReason& ar) const {

}
