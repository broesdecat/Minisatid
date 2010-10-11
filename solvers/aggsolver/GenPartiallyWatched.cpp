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
	if(set.size()>1){
		set[index] = set[set.size()-1];
	}
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


GenPWAgg::GenPWAgg(paggs agg): PWAgg(agg), headprop(false){
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

lbool GenPWAgg::isKnown(watchset w, const Agg& agg, const vpgpw& set, const vpgpw& watches){
	if(w==NT){
		Weight max = as().getESV();
		for(vpgpw::const_iterator i=set.begin(); i<set.end(); i++){
			const WL& wl = (*i)->getWL();
			if((*i)->isMonotone()){
				max = add(max, wl);
			}
		}
		for(vpgpw::const_iterator i=watches.begin(); i<watches.end(); i++){
			const WL& wl = (*i)->getWL();
			if((*i)->getPos()==POSSETUNKN){
				if((*i)->isMonotone()){
					max = add(max, wl);
				}
			}else{
				if(!(*i)->isMonotone() && propagatedValue(wl)!=l_False){
					max = add(max, wl);
				}
				if((*i)->isMonotone() && propagatedValue(wl)==l_True){
					max = add(max, wl);
				}
			}
		}
		reportf("Max value is %d\n", max);
		if(!isSatisfied(agg, max)){
			return l_False;
		}else{
			return l_Undef;
		}
	}else{
		Weight min = as().getESV();
		for(vpgpw::const_iterator i=set.begin(); i<set.end(); i++){
			const WL& wl = (*i)->getWL();
			if(!(*i)->isMonotone()){
				min = add(min, wl);
			}
		}
		for(vpgpw::const_iterator i=watches.begin(); i<watches.end(); i++){
			const WL& wl = (*i)->getWL();
			if((*i)->getPos()==POSSETUNKN){
				if(!(*i)->isMonotone()){
					min = add(min, wl);
				}
			}else{
				if((*i)->isMonotone() && propagatedValue(wl)!=l_False){
					min = add(min, wl);
				}
				if(!(*i)->isMonotone() && propagatedValue(wl)==l_True){
					min = add(min, wl);
				}
			}
		}
		reportf("Min value is %d\n", min);
		if(isSatisfied(agg, min)){
			return l_True;
		}else{
			return l_Undef;
		}
	}
}

rClause GenPWAgg::reconstructSet(const Agg& agg, watchset w, pgpw watch, bool& propagations){
	vpgpw& set = getSet(w);
	vpgpw& watches = getWatches(w);

	assert(set.size()+watches.size()==as().getWL().size());

	lbool until = isNonFalseCheck(w)?l_True:l_False;

	rClause confl = nullPtrClause;

	if(propagatedValue(agg.getHead())==l_Undef){
		reportf("Constructing basic\n");
		for(vsize i=0; isKnown(w, agg, set, watches)!=until && i<set.size();){
			if(((isNonFalseCheck(w) && set[i]->isMonotone()) || (!isNonFalseCheck(w) && !set[i]->isMonotone())) && propagatedValue(set[i]->getWL())!=l_False){
				reportf("    added to posinset\n");
				addToWatchedSet(w, i, POSINSET);
			}else if(((isNonFalseCheck(w) && !set[i]->isMonotone()) || (!isNonFalseCheck(w) && set[i]->isMonotone())) && propagatedValue(set[i]->getWL())!=l_True){
				reportf("    added to posoutset\n");
				addToWatchedSet(w, i, POSOUTSET);
			}else{
				i++; //TODO save last i to start from there i cyclic search
			}
		}
		if(isKnown(w, agg, set, watches)!=until){
			Lit prophead = isNonFalseCheck(w)?~agg.getHead():agg.getHead();
			Lit watchlit = watch!=NULL?watch->getWatchLit():mkLit(-1);
			propagations = true;
			headprop = true;
			confl = notifySolver(new AggReason(agg, watchlit, isNonFalseCheck(w)?BASEDONCC:BASEDONCP, prophead, true));
		}
	}else{
		int origsize = watches.size();
		reportf("Constructing extension\n");

		/*reportf("Before\n");
		for(int i=0; i<watches.size(); i++){
			reportf("watch "); gprintLit(watches[i]->getWatchLit()); reportf(" %s\n", watches[i]->getPos()==POSSETUNKN?"unknown":"not unknown");
		}*/

		for(vsize i=0; confl==nullPtrClause && i<origsize; i++){
			POSS temp = watches[i]->getPos();
			watches[i]->setPos(POSSETUNKN);

			for(vsize j=0; isKnown(w, agg, set, watches)!=until && j<set.size();){
				if(((isNonFalseCheck(w) && set[j]->isMonotone()) || (!isNonFalseCheck(w) && !set[j]->isMonotone())) && propagatedValue(set[j]->getWL())!=l_False){
					reportf("    added to posinset\n");
					addToWatchedSet(w, j, POSINSET);
				}else if(((isNonFalseCheck(w) && !set[j]->isMonotone()) || (!isNonFalseCheck(w) && set[j]->isMonotone())) && propagatedValue(set[j]->getWL())!=l_True){
					reportf("    added to posoutset\n");
					addToWatchedSet(w, j, POSOUTSET);
				}else{
					j++;
				}
			}

			if(isKnown(w, agg, set, watches)!=until){
				reportf("No replacement found for "); gprintLit(watches[i]->getWatchLit()); reportf("\n");
				Lit watchlit = watch!=NULL?watch->getWatchLit():mkLit(-1);
				propagations = true;
				confl = notifySolver(new AggReason(agg, watchlit, isNonFalseCheck(w)?BASEDONCC:BASEDONCP, ~watches[i]->getWatchLit(), false));
			}else{
				reportf("Replacement found for "); gprintLit(watches[i]->getWatchLit()); reportf(" or still valid\n");
			}

			watches[i]->setPos(temp);

			/*reportf("After\n");
			for(int i=0; i<watches.size(); i++){
				reportf("watch "); gprintLit(watches[i]->getWatchLit());
				reportf(" %s, ", watches[i]->getPos()==POSSETUNKN?"unknown":"not unknown");
				reportf(" with index %d found on pos %d\n", watches[i]->getIndex(), i);
			}*/
		}
	}

#ifdef DEBUG
	assert(set.size()+watches.size()==as().getWL().size());
	for(int i=0; i<set.size(); i++){
		assert(set[i]->getPos()==POSSETUNKN);
	}
	for(int i=0; i<watches.size(); i++){
		assert(watches[i]->getPos()!=POSSETUNKN || watches[i]==watch);
		assert(watches[watches[i]->getIndex()]==watches[i]);
	}
#endif

	return confl;
}

rClause GenPWAgg::propagate(const Lit& p, Watch* watch) {
	assert(getSet(NF).size()+getWatches(NF).size()==as().getWL().size() || !checking(NF));
	assert(getSet(NT).size()+getWatches(NT).size()==as().getWL().size() || !checking(NT));
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

	//Remove watch from setpos at start:
	POSS temp = pw->getPos();
	pw->setPos(POSSETUNKN); //TODO maybe even better make it negation?

	bool propagations = false;
	watchset w = pw->getWatchset();
	confl = reconstructSet(*as().getAgg()[0], w, pw, propagations); //TODO multi agg
	if(!propagations){
		//Remove watch from the watched set
		vpgpw& set = getSet(w);
		vpgpw& watches = getWatches(w);
		if(watches.size()>1){
			reportf("Moving: "); gprintLit(pw->getWatchLit()); reportf("\n");
			int index = pw->getIndex();
			watches[index] = watches[watches.size()-1];
			watches[index]->setIndex(index);
		}
		pw->removedFromSet();
		set.push_back(pw);
		watches.pop_back();
	}else{
		//add watch back to original pos
		pw->setPos(temp);
	}
	if(confl==nullPtrClause){
		addWatchesToNetwork(w);
	}


	assert(pw->getWatchset()==INSET || getWatches(pw->getWatchset())[pw->getIndex()]==pw);
	assert(getSet(NF).size()+getWatches(NF).size()==as().getWL().size() || !checking(NF));
	assert(getSet(NT).size()+getWatches(NT).size()==as().getWL().size() || !checking(NT));

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
	addWatchesToNetwork(w);

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
