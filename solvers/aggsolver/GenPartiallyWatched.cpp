/*
 * PartiallyWatched.cpp
 *
 *  Created on: Sep 14, 2010
 *      Author: broes
 */

#include "solvers/aggsolver/PartiallyWatched.hpp"

#include "solvers/aggsolver/AggSolver.hpp"
#include "solvers/pcsolver/PCSolver.hpp"

#include <stdint.h>
#include <inttypes.h>
#include <limits.h>

inline vpgpw& GenPWAgg::getSet(watchset w) {
	switch (w) {
	case NF:
		return setf;
		break;
	case NT:
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
		addWatchToNetwork(*i);
	}
}

/*
 * Removes a literal from its set and adds it to a watched set
 */
void GenPWAgg::addWatchToNetwork(pgpw watch){
	if(watch->getWatchset()!=INSET && !watch->isInUse()){
		watch->setInUse(true);
		getSolver()->addTempWatch(watch->getWatchLit(), watch);
	}
}


GenPWAgg::GenPWAgg(paggs agg): PWAgg(agg){
}

GenPWAgg::~GenPWAgg(){
	deleteList<GenPWatch>(nf);
	deleteList<GenPWatch>(setf);
	deleteList<GenPWatch>(nt);
	deleteList<GenPWatch>(sett);
}

void GenPWAgg::initialize(bool& unsat, bool& sat) {
	vpagg& aggs = as().getRefAgg();

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

	bool propagations = false;

	rClause confl = reconstructSet(agg, NF, NULL, propagations);
	if(confl!=nullPtrClause){ unsat = true; sat = false; return; }
	if(propagations){ unsat = false; sat = true; return; }

	confl = reconstructSet(agg, NT, NULL, propagations);
	if(confl!=nullPtrClause){ unsat = true; sat = false; return; }
	if(propagations){ unsat = false; sat = true; return; }

	//IMPORTANT: only add watches AFTER initialization, otherwise delete is not complete!
	addWatchesToNetwork(NF);
	addWatchesToNetwork(NT);

#ifdef DEBUG
	for(int i=0; i<getSet(NF).size(); i++){
		assert(getSet(NF)[i]->getPos()==POSSETUNKN);
	}
	for(int i=0; i<getSet(NT).size(); i++){
		assert(getSet(NT)[i]->getPos()==POSSETUNKN);
	}
#endif

	PWAgg::initialize(unsat, sat);
}

void GenPWAgg::adaptMinMax(vpgpw::const_iterator i, Weight & min, Weight & max){
	const WL & wl = (*i)->getWL();
	if(propagatedValue(wl) == l_True){ //It is in the set
		min = add(min, wl);
		max = add(max, wl);
	}else if(propagatedValue(wl) == l_Undef){ //It might be in the set
		if((*i)->getPos() == POSINSET){
			min = add(min, wl);
			max = add(max, wl);
		}else if((*i)->getPos() == POSSETUNKN){
			if((*i)->isMonotone()){
				max = add(max, wl);
			}else{
				min = add(min, wl);
			}
		}
    } //not in the set does not have to be treated!
}

lbool GenPWAgg::isKnown(const Agg& agg, const vpgpw& set, const vpgpw& set2){
	Weight min = as().getESV();
	Weight max = as().getESV();
	for(vpgpw::const_iterator i=set.begin(); i<set.end(); i++){
		adaptMinMax(i, min, max);
	}
	for(vpgpw::const_iterator i=set2.begin(); i<set2.end(); i++){
		adaptMinMax(i, min, max);
	}
	if(isSatisfied(agg, min)){
		assert(isSatisfied(agg, max));
		return l_True;
	}else if(!isSatisfied(agg, max)){
		assert(!isSatisfied(agg, min));
		return l_False;
	}else{
		return l_Undef;
	}
}

rClause GenPWAgg::reconstructSet(const Agg& agg, watchset w, pgpw watch, bool& propagations){
	vpgpw& set = getSet(w);
	vpgpw& watches = getWatches(w);
	lbool until = isNonFalseCheck(w)?l_True:l_False;

	rClause confl = nullPtrClause;

	if(propagatedValue(agg.getHead())==l_Undef){
		for(vsize i=0; isKnown(agg, set, watches)!=until && i<set.size();){
			if(((isNonFalseCheck(w) && set[i]->isMonotone()) || (!isNonFalseCheck(w) && !set[i]->isMonotone())) && propagatedValue(set[i]->getWL())!=l_False){
				addToWatchedSet(w, i, POSINSET);
			}else if(((isNonFalseCheck(w) && !set[i]->isMonotone()) || (!isNonFalseCheck(w) && set[i]->isMonotone())) && propagatedValue(set[i]->getWL())!=l_True){
				addToWatchedSet(w, i, POSOUTSET);
			}else{
				i++; //TODO save last i to start from there i cyclic search
			}
		}
		if(isKnown(agg, set, watches)!=until){
			Lit prophead = isNonFalseCheck(w)?~agg.getHead():agg.getHead();
			Lit watchlit = watch!=NULL?watch->getWatchLit():mkLit(-1);
			propagations = true;
			confl = notifySolver(new AggReason(agg, watchlit, isNonFalseCheck(w)?BASEDONCC:BASEDONCP, prophead, true));
			if(confl!=nullPtrClause){ return confl; }
		}
	}else{
		int origsize = watches.size();
		for(vsize i=0; i<origsize; i++){
			POSS temp = watches[i]->getPos();
			watches[i]->setPos(POSSETUNKN);

			for(vsize j=0; isKnown(agg, set, watches)!=until && j<set.size();){
				if(((isNonFalseCheck(w) && set[j]->isMonotone()) || (!isNonFalseCheck(w) && !set[j]->isMonotone())) && propagatedValue(set[j]->getWL())!=l_False){
					addToWatchedSet(w, j, POSINSET);
				}else if(((isNonFalseCheck(w) && !set[j]->isMonotone()) || (!isNonFalseCheck(w) && set[j]->isMonotone())) && propagatedValue(set[j]->getWL())!=l_True){
					addToWatchedSet(w, j, POSOUTSET);
				}else{
					j++;
				}
			}

			if(isKnown(agg, set, watches)!=until){
				Lit watchlit = watch!=NULL?watch->getWatchLit():mkLit(-1);
				propagations = true;
				confl = notifySolver(new AggReason(agg, watchlit, isNonFalseCheck(w)?BASEDONCC:BASEDONCP, ~watches[i]->getWatchLit(), false));
				if(confl!=nullPtrClause){ return confl; }
			}

			watches[i]->setPos(temp);
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

	return confl;
}

rClause GenPWAgg::propagate(const Lit& p, Watch* watch) {
	rClause confl = nullPtrClause;
	if(headprop){ return confl;	}

	GenPWatch* pw = dynamic_cast<GenPWatch*>(watch);
	assert(pw->isInUse());

	pw->setInUse(false);

	if(pw->getWatchset()==INSET){
		assert(pw->getIndex()==-1);
		return confl;
	}else{
		assert(pw->getIndex()!=-1);
	}

	//Remove watch at start: not necessary, because it will be handled by its truth value
	bool propagations = false;
	confl = reconstructSet(*as().getAgg()[0], pw->getWatchset(), pw, propagations); //TODO multi agg
	if(confl!=nullPtrClause && !propagations){
		//Remove watch from the watched set
		reportf("Removing watch from set\n");
		vpgpw& watches = getWatches(pw->getWatchset());
		pw->removedFromSet();
		watches[pw->getIndex()] = watches[watches.size()-1];
		watches.pop_back();
	}else{
		//add watch back to network
		reportf("Adding watch back to set\n");
		addWatchToNetwork(pw);
	}

	assert(pw->getWatchset()==INSET || getWatches(pw->getWatchset())[pw->getIndex()]==pw);

	return confl;
}

rClause GenPWAgg::propagate(const Agg& agg) {
	rClause confl = nullPtrClause;

	//IMPORTANT: necessary for correctness!
	if(headprop){ return confl;	}

	watchset w  = NF;
	if(!checking(w)){
		w = NT;
		assert(checking(w));
	}

	removeWatchesFromSet(w==NF?NT:NF);

	bool propagations = false;
	confl = reconstructSet(*as().getAgg()[0], w, NULL, propagations); //TODO multi agg
	if(confl==nullPtrClause){
		addWatchesToNetwork(w);
	}

	return confl;
}

void GenPWAgg::backtrack(const Agg& agg) {
	headprop = false;

	watchset w  = NF;
	if(!checking(w)){
		w = NT;
		assert(checking(w));
	}

	bool propagations = false;
	rClause confl = reconstructSet(*as().getAgg()[0], w, NULL, propagations); //TODO multi agg
	assert(confl==nullPtrClause && !propagations);
	addWatchesToNetwork(w);
}

void GenPWAgg::getExplanation(vec<Lit>& lits, const AggReason& ar) const {
	//TODO do check agg until satisfied!
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
