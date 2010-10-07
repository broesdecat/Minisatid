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
	lbool headvalue = propagatedValue(as().getAgg()[0]->getHead());
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
	}
}


/*
 * index is the index in the original set, from which it should be removed
 * w indicates the set to which it should be added
 */
void GenPWAgg::addToWatchedSet(watchset w, vsize index, POSS p){
	vpgpw& set = getSet(w);
	vpgpw& watches = getWatches(w);
	pgpw watch = set[index];
	watches.push_back(watch);
	set[index] = set[set.size()-1];
	set.pop_back();

	watch->setPos(p);
	watch->pushIntoSet(w, watches.size()-1);
}

void GenPWAgg::removeWatchesFromSet(watchset w){
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
	nffailed = !reconstructBasicSet(agg, NF);
	ntfailed = !reconstructBasicSet(agg, NT);

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

bool GenPWAgg::reconstructBasicSet(const Agg& agg, watchset w, pgpw watch){
	assert(!isEx(w));

	vpgpw& set = getSet(w);
	vpgpw& watches = getWatches(w);

	vpgpw ss;
	if(watch!=NULL){
		ss.push_back(watch);
	}
	ss.insert(ss.begin(), set.begin(), set.end());
	ss.insert(ss.begin(), watches.begin(), watches.end());

	lbool until = isF(w)?l_True:l_False;
	for(vsize i=0; isKnown(agg, ss)!=until && i<set.size();){
		if(((isF(w) && set[i]->isMonotone()) || (!isF(w) && !set[i]->isMonotone())) && propagatedValue(set[i]->getWL())!=l_False){
			addToWatchedSet(w, i, POSINSET);
		}else if(((isF(w) && !set[i]->isMonotone()) || (!isF(w) && set[i]->isMonotone())) && propagatedValue(set[i]->getWL())!=l_True){
			addToWatchedSet(w, i, POSOUTSET);
		}else{
			i++;
		}
	}

#ifdef DEBUG
	for(int i=0; i<set.size(); i++){
		assert(set[i]->getPos()==POSSETUNKN);
	}
	for(int i=0; i<watches.size(); i++){
		assert(watches[i]->getPos()!=POSSETUNKN);
	}
#endif

	return (isKnown(agg, ss)==until);
}

vpgpw GenPWAgg::reconstructExSet(const Agg& agg, watchset w, pgpw watch){
	assert(isEx(w));

	vpgpw& set = getSet(w);
	vpgpw& watches = getWatches(w);
	vpgpw& origwatches = getWatches(isF(w)?NF:NT);

	lbool until = isF(w)?l_True:l_False;

	vpgpw proplist; //list of forced propagations

	vpgpw ss;
	if(watch!=NULL){
		ss.push_back(watch);
	}
	ss.insert(ss.begin(), set.begin(), set.end());
	ss.insert(ss.begin(), origwatches.begin(), origwatches.end());
	ss.insert(ss.begin(), watches.begin(), watches.end());

	for(vsize i=0; i<origwatches.size(); i++){
		POSS temp = origwatches[i]->getPos();
		origwatches[i]->setPos(POSSETUNKN);

		for(vsize j=0; isKnown(agg, ss)!=until && j<set.size();){
			if(((isF(w) && set[j]->isMonotone()) || (!isF(w) && !set[j]->isMonotone())) && propagatedValue(set[j]->getWL())!=l_False){
				addToWatchedSet(w, j, POSINSET);
			}else if(((isF(w) && !set[j]->isMonotone()) || (!isF(w) && set[j]->isMonotone())) && propagatedValue(set[j]->getWL())!=l_True){
				addToWatchedSet(w, j, POSOUTSET);
			}else{
				j++;
			}
		}

		if(isKnown(agg, ss)!=until){
			proplist.push_back(origwatches[i]);
		}

		origwatches[i]->setPos(temp);
	}

#ifdef DEBUG
	for(int i=0; i<set.size(); i++){
		assert(set[i]->getPos()==POSSETUNKN);
	}
	for(int i=0; i<watches.size(); i++){
		assert(watches[i]->getPos()!=POSSETUNKN);
	}
	for(int i=0; i<origwatches.size(); i++){
		assert(origwatches[i]->getPos()!=POSSETUNKN);
	}
#endif

	return proplist;
}

void GenPWAgg::replace(vsize index, watchset w) {
	const Agg& agg = *as().getAgg()[0];

	vpgpw& watches = getWatches(w);
	pgpw watch = watches[index];

	//Remove watch from the set
	watch->removedFromSet();
	watches[index] = watches[watches.size()-1];
	watches.pop_back();

	bool addwatchback = false;
	if(propagatedValue(agg.getHead())==l_Undef){
		bool found = reconstructBasicSet(agg, w, watch);
		if(!found){
			addwatchback = true;
			//TODO propagate head
		}
	}else{
		if(!isEX(w)){
			watchset w2 = w==NFEX?NF:NT;
			vpgpw& origwatches = getWatches(w2);
			for(int i=0; i<watches.size(); i++){
				pgpw temp = watches[i];
				origwatches.push_back(temp);
				temp->pushIntoSet(w2, origwatches.size()-1);
			}
			watches.clear();
			w = w2;
		}
		vpgpw props = reconstructExSet(agg, w, watch);
		if(props.size()!=0 && isEX(w)){
			addwatchback = true;
		}
		//TODO propagate all derivations
	}

	if(addwatchback){
		//add watch back to w
		watches.push_back(watch);
		watch->pushIntoSet(w, watches.size()-1);

	}
}

rClause GenPWAgg::propagate(const Lit& p, Watch* watch) {
	rClause confl = nullPtrClause;
	if(headprop){
		return confl;
	}

	GenPWatch* pw = dynamic_cast<GenPWatch*>(watch);

	assert(pw->setInUse(true));

	if(pw->getWatchset()==INSET){
		pw->setInUse(false);
		assert(w.getIndex()==-1);
		return confl;
	}else{
		assert(w.getIndex()!=-1);
	}

	replace(pw->getIndex(), pw->getWatchset());

	assert(w.getWatchset()==INSET || getWatches(w.getWatchset())[w.getIndex()]->watch()==pw);

	return confl;
}

rClause GenPWAgg::propagate(const Agg& agg) {
	rClause confl = nullPtrClause;

	if(headprop){ //IMPORTANT: necessary for correctness!
		return confl;
	}

	assert(nfex.size() == 0 && ntex.size() == 0);

	watchset w = NF;
	if(checking(w)){
		removeWatchesFromSet(w);
	}

	w = NT;
	if(checking(w)){
		removeWatchesFromSet(w);
	}

	vpgpw props;
	w  = NFEX;
	if (checking(NFEX)) {
		w = NFEX;
	}else{
		w = NTEX;
	}

	props = reconstructExSet(agg, w);
	if (props.size()>0) {
		const vpgpw& watches = getWatches(w);
		for (vpgpw::const_iterator i = watches.begin(); confl == nullPtrClause && i < watches.end(); i++) {
			confl = as().getSolver()->notifySolver(new AggReason(*as().getAgg()[0], propagatedValue(agg.getHead())==l_True?agg.getHead():~agg.getHead(), w==NFEX?BASEDONCC:BASEDONCP, ~(*i)->getWatchLit(), false));
		}
	}
	addWatchesToNetwork(w);

	return confl;
}

void GenPWAgg::backtrack(const Agg& agg) {
	headprop = false;

	watchset w = NFEX;
	if (checking(w)) {
		removeWatchesFromSet(w);
	}

	w = NTEX;
	if (checking(w)) {
		removeWatchesFromSet(w);
	}

	w  = NF;
	if(checking(w)){
		reconstructBasicSet(*as().getAgg()[0], w);
		addWatchesToNetwork(w);
	}

	w = NT;
	if(checking(w)){
		reconstructBasicSet(*as().getAgg()[0], w);
		addWatchesToNetwork(w);
	}
}

void GenPWAgg::getExplanation(vec<Lit>& lits, const AggReason& ar) const {
	//If toInt(Lit) is negative, it indicates that the literal is entailed by an empty partial interpretation, so the reason clause is empty
	if(toInt(ar.getLit())<0){
		return;
	}

	lits.push(~ar.getLit());

	const PCSolver& pcsol = *as().getSolver()->getPCSolver();
	const Lit& head = ar.getAgg().getHead();
	if(value(head)!=l_Undef && var(ar.getLit())!=var(head)){
		if(pcsol.assertedBefore(var(head), var(ar.getLit()))){
			lits.push(value(head)==l_True?~head:head);
		}
	}

	Lit comparelit = ar.getLit();
	if(var(ar.getLit())==var(head)){
		comparelit = ar.getPropLit();
	}

	for (vsize i = 0; i < as().getWL().size(); i++) {
		const WL& wl = as().getWL()[i];
		if(ar.getExpl()==BASEDONCC){ //Monotone one (one in the set) propagated: take only false monotone ones
			if(value(wl.getLit())==(ar.getAgg().isUpper()?l_True:l_False)){
				continue;
			}
		}
		if(ar.getExpl()==BASEDONCP){ //Anti-monotone one (one not in the set) propagated: take only true monotone ones
			if(value(wl.getLit())==(ar.getAgg().isUpper()?l_False:l_True)){
				continue;
			}
		}
		if (var(wl.getLit()) != var(comparelit) && value(wl.getLit()) != l_Undef) {
			if(pcsol.assertedBefore(var(wl.getLit()), var(comparelit))){
				lits.push(value(wl.getLit())==l_True?~wl.getLit():wl.getLit());
			}
		}
	}
}
