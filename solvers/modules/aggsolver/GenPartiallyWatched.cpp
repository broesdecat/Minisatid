///*
// * PartiallyWatched.cpp
// *
// *  Created on: Sep 14, 2010
// *      Author: broes
// */
//
//#include "solvers/modules/aggsolver/PartiallyWatched.hpp"
//
//#include "solvers/modules/AggSolver.hpp"
//#include "solvers/theorysolvers/PCSolver.hpp"
//
//#include <stdint.h>
//#include <inttypes.h>
//#include <limits.h>
//
//using namespace std;
//using namespace MinisatID;
//
//inline vpgpw& GenPWAgg::getSet(watchset w) {
//	switch (w) {
//	case NF:
//		return setf;
//		break;
//	case NT:
//		return sett;
//		break;
//	default:
//		assert(false);
//		exit(-1);
//	}
//}
//
//inline vpgpw& GenPWAgg::getWatches(watchset w) {
//	switch (w) {
//	case NF:
//		return nf;
//		break;
//	case NT:
//		return nt;
//		break;
//	default:
//		assert(false);
//		exit(-1);
//	}
//}
//
///*inline bool GenPWAgg::checking(watchset w) const{
//	lbool headvalue = propagatedValue(as().getAgg()[0]->getHead());
//	switch (w) {
//	case NF:
//		return headvalue!=l_False;
//		break;
//	case NT:
//		return headvalue!=l_True;
//		break;
//	default:
//		assert(false);
//		exit(-1);
//	}
//}*/
//
//
///*
// * index is the index in the original set, from which it should be removed
// * w indicates the set to which it should be added
// */
//void GenPWAgg::addToWatchedSet(watchset w, vsize index){
//	vpgpw& set = getSet(w);
//	vpgpw& watches = getWatches(w);
//	pgpw watch = set[index];
//	watches.push_back(watch);
//	if(set.size()>1){
//		set[index] = set[set.size()-1];
//	}
//	set.pop_back();
//
//	watch->pushIntoSet(w, watches.size()-1);
//}
//
///**
// * @pre: one watch should be moved from a watched set to a nonwatched set
// */
//void GenPWAgg::removeFromWatchedSet(pgpw pw){
//	watchset w = pw->getWatchset();
//	vpgpw& set = getSet(w);
//	vpgpw& watches = getWatches(w);
//
//	if(watches.size()>1){
//		int index = pw->getIndex();
//		watches[index] = watches[watches.size()-1];
//		watches[index]->setIndex(index);
//	}
//	set.push_back(pw);
//	watches.pop_back();
//
//	pw->removedFromSet();
//}
//
///**
// * @pre: all watches from a watch set should be moved to the non-watched set
// */
//void GenPWAgg::removeAllFromWatchedSet(watchset w){
//	vpgpw& set = getSet(w);
//	vpgpw& watches = getWatches(w);
//
//	for(vpgpw::const_iterator i=watches.begin(); i<watches.end(); i++){
//		(*i)->removedFromSet();
//		set.push_back(*(i));
//	}
//	watches.clear();
//}
//
///*
// * Removes a literal from its set and adds it to a watched set
// */
//void GenPWAgg::addWatchToNetwork(pgpw watch){
//	if(watch->getWatchset()!=INSET && !watch->isInUse()){
//		watch->setInUse(true);
//		getSolver()->addTempWatch(watch->getWatchLit(), watch);
//	}
//}
//
//void GenPWAgg::addWatchesToNetwork(watchset w){
//	for(vpgpw::const_iterator i=getWatches(w).begin(); i<getWatches(w).end(); i++){
//		addWatchToNetwork(*i);
//	}
//}
//
//
//GenPWAgg::GenPWAgg(paggs agg): PWAgg(agg), headprop(false){}
//
//CardGenPWAgg::CardGenPWAgg(paggs agg):GenPWAgg(agg){}
//
//SumGenPWAgg::SumGenPWAgg(paggs agg):GenPWAgg(agg){}
//
//GenPWAgg::~GenPWAgg(){
//	deleteList<GenPWatch>(nf);
//	deleteList<GenPWatch>(setf);
//	deleteList<GenPWatch>(nt);
//	deleteList<GenPWatch>(sett);
//}
//
//void GenPWAgg::initialize(bool& unsat, bool& sat) {
//	vpagg& aggs = as().getRefAgg();
//
//	if (aggs.size() == 0) {
//		sat = true;
//		return;
//	}
//	as().doSetReduction();
//
//	//Verify all aggregates have the same sign:
//	chosensign = aggs[0]->getSign();
//	/*for(int i=1; i<aggs.size(); i++){
//		if(sign!=aggs[i]->getSign()){
//			throw idpexception("The aggregates added to genpwagg do not consistenly have the same type!\n");
//		}
//	}*/
//
//	//Create sets and watches, initialize min/max values
//	for(vsize i=0; i<as().getWL().size(); i++){
//		const WL& wl = as().getWL()[i];
//		if(as().isMonotone(*aggs[0], wl)){
//			setf.push_back(new GenPWatch(asp(), wl, true, true));
//			sett.push_back(new GenPWatch(asp(), wl, false, true));
//		}else{
//			setf.push_back(new GenPWatch(asp(), wl, false, false));
//			sett.push_back(new GenPWatch(asp(), wl, true, false));
//		}
//	}
//
//	//Initialize NF and NT (all literals are still false!)
//
//	bool propagations = false;
//
//	vpagg aggsleft;
//	for(int i=0; i<aggs.size(); i++){
//		//TODO SET REDUCTION IS NOT DONE HERE!
//		rClause confl = reconstructSet(*aggs[i], NF, NULL, propagations);
//		if(confl!=nullPtrClause){ unsat = true; sat = false; return; }
//		if(propagations){
//			continue;
//		}
//
//		confl = reconstructSet(*aggs[i], NT, NULL, propagations);
//		if(confl!=nullPtrClause){ unsat = true; sat = false; return; }
//		if(propagations){
//			continue;
//		}
//		aggsleft.push_back(aggs[i]);
//	}
//	aggs.clear();
//	aggs.insert(aggs.begin(), aggsleft.begin(), aggsleft.end());
//
//	if(aggs.size()==0){ unsat = false; sat = true; return; }
//
//	//IMPORTANT: only add watches AFTER initialization, otherwise delete is not complete!
//	addWatchesToNetwork(NF);
//	addWatchesToNetwork(NT);
//
//	PWAgg::initialize(unsat, sat);
//}
//
//
//void GenPWAgg::adaptValue(watchset w, const vpgpw& set, Weight& val) const{
//	for(vpgpw::const_iterator i=set.begin(); i<set.end(); i++){
//		const WL& wl = (*i)->getWL();
//		bool mono = (*i)->isMonotone();
//		if((*i)->treatAsKnown()){
//			if(((w==NT && !mono) || (w==NF && mono)) && propagatedValue(wl)!=l_False){
//				val = add(val, wl);
//			}
//			if(((w==NT && mono) || (w==NF && !mono)) && propagatedValue(wl)==l_True){
//				val = add(val, wl);
//			}
//		}else{
//			if((w==NT && mono) || (w==NF && !mono)){
//				val = add(val, wl);
//			}
//		}
//	}
//}
//
//lbool GenPWAgg::isKnown(watchset w, const Agg& agg, const vpgpw& set, const vpgpw& watches) const{
//	Weight val = as().getESV();
//	adaptValue(w, set, val);
//	adaptValue(w, watches, val);
//	if(w==NT && !isSatisfied(agg, val)){
//		return l_False;
//	}else if(w==NF && isSatisfied(agg, val)){
//		return l_True;
//	}else{
//		return l_Undef;
//	}
//}
//
//rClause GenPWAgg::reconstructSet(const Agg& agg, watchset w, pgpw watch, bool& propagations){
//	if(agg.getSign()!=chosensign){
//		w = w==NF?NT:NF;
//	}
//
//	vpgpw& set = getSet(w);
//	vpgpw& watches = getWatches(w);
//
//	lbool until = isNonFalseCheck(w)?l_True:l_False;
//
//	rClause confl = nullPtrClause;
//
//	lbool headvalue = propagatedValue(agg.getHead());
//
//	if((headvalue==l_True && w==NT) || (headvalue==l_False && w==NF)){
//		return confl;
//	}
//
//	if(headvalue==l_Undef){
//		for(vsize i=0; isKnown(w, agg, set, watches)!=until && i<set.size();){
//			if(((isNonFalseCheck(w) && set[i]->isMonotone()) || (!isNonFalseCheck(w) && !set[i]->isMonotone())) && propagatedValue(set[i]->getWL())!=l_False){
//				addToWatchedSet(w, i);
//			}else if(((isNonFalseCheck(w) && !set[i]->isMonotone()) || (!isNonFalseCheck(w) && set[i]->isMonotone())) && propagatedValue(set[i]->getWL())!=l_True){
//				addToWatchedSet(w, i);
//			}else{
//				i++; //TODO save last i to start from there i cyclic search
//			}
//		}
//		if(isKnown(w, agg, set, watches)!=until){
//			Lit prophead = isNonFalseCheck(w)?~agg.getHead():agg.getHead();
//			Lit watchlit = watch!=NULL?watch->getWatchLit():mkLit(-1);
//			propagations = true;
//			confl = notifySolver(new AggReason(agg, watchlit, isNonFalseCheck(w)?BASEDONCC:BASEDONCP, prophead, true));
//		}
//	}else{
//		int origsize = watches.size();
//
//		for(vsize i=0; confl==nullPtrClause && i<origsize; i++){
//			watches[i]->setTreatAsKnown(false);
//
//			for(vsize j=0; isKnown(w, agg, set, watches)!=until && j<set.size();){
//				if(((isNonFalseCheck(w) && set[j]->isMonotone()) || (!isNonFalseCheck(w) && !set[j]->isMonotone())) && propagatedValue(set[j]->getWL())!=l_False){
//					addToWatchedSet(w, j);
//				}else if(((isNonFalseCheck(w) && !set[j]->isMonotone()) || (!isNonFalseCheck(w) && set[j]->isMonotone())) && propagatedValue(set[j]->getWL())!=l_True){
//					addToWatchedSet(w, j);
//				}else{
//					j++;
//				}
//			}
//
//			if(isKnown(w, agg, set, watches)!=until){
//				Lit watchlit = watch!=NULL?watch->getWatchLit():mkLit(-1);
//				propagations = true;
//				//FIXME important: notifysolver might lead to backtrack! So should be ready to backtrack!:
//				watches[i]->setTreatAsKnown(true);
//
//				confl = notifySolver(new AggReason(agg, watchlit, isNonFalseCheck(w)?BASEDONCC:BASEDONCP, ~watches[i]->getWatchLit(), false));
//			}
//
//			watches[i]->setTreatAsKnown(true);
//		}
//	}
//
//#ifdef DEBUG
//	assert(set.size()+watches.size()==as().getWL().size());
//	for(int i=0; i<set.size(); i++){
//		assert(!set[i]->treatAsKnown());
//	}
//	for(int i=0; i<watches.size(); i++){
//		assert(watches[i]->treatAsKnown() || (watches[i]==watch && !watches[i]->treatAsKnown()));
//		assert(watches[watches[i]->getIndex()]==watches[i]);
//	}
//#endif
//
//	return confl;
//}
//
//rClause GenPWAgg::propagate(const Lit& p, Watch* watch) {
//	rClause confl = nullPtrClause;
//
//	GenPWatch* const pw = dynamic_cast<GenPWatch*>(watch);
//
//	assert(pw->isInUse());
//	pw->setInUse(false);
//
//	if(pw->getWatchset()==INSET){
//		assert(pw->getIndex()==-1);
//		return confl;
//	}else{
//		assert(pw->getIndex()!=-1);
//	}
//
//	watchset w = pw->getWatchset();
//
//	//Remove watch from setpos at start:
//	pw->setTreatAsKnown(false);
//
//	bool propagations = false;
//	for(int i=0; confl==nullPtrClause && i<as().getAgg().size(); i++){
//		confl = reconstructSet(*as().getAgg()[i], w, pw, propagations);
//	}
//
//	if(!propagations){
//		removeFromWatchedSet(pw);
//	}else{
//		//add watch back to original pos unless it was removed from the watched
//		pw->setTreatAsKnown(true);
//	}
//
//	addWatchesToNetwork(w);//TODO is this correct?
//
//	assert(pw->getWatchset()==INSET || getWatches(pw->getWatchset())[pw->getIndex()]==pw);
//
//	return confl;
//}
//
//rClause GenPWAgg::propagate(const Agg& agg) {
//	rClause confl = nullPtrClause;
//
//	//TODO FIXME: mimic headprop by verifying that the head could be propagated here!
//
//	/*watchset w  = NF;
//	if(!checking(w)){
//		w = NT;
//		assert(checking(w));
//	}
//
//	removeAllFromWatchedSet(w==NF?NT:NF);*/
//
//	watchset w = propagatedValue(agg.getHead())==l_True?NF:NT;
//
//	bool propagations = false;
//	confl = reconstructSet(agg, w, NULL, propagations);
//	addWatchesToNetwork(w); //TODO should this happen before or after checking for conflicts?
//
//	return confl;
//}
//
//void GenPWAgg::backtrack(const Agg& agg) {
//	/*watchset w  = NF;
//	if(!checking(w)){
//		w = NT;
//		assert(checking(w));
//	}*/
//
//	bool propagations = false;
//	rClause confl = reconstructSet(agg, NF, NULL, propagations);
//	assert(confl==nullPtrClause && !propagations);
//	addWatchesToNetwork(NF);
//
//	propagations = false;
//	confl = reconstructSet(agg, NT, NULL, propagations);
//	assert(confl==nullPtrClause && !propagations);
//	addWatchesToNetwork(NT);
//}
//
//void GenPWAgg::getExplanation(vec<Lit>& lits, const AggReason& ar) const {
//	//TODO do check agg until satisfied!
//	//If toInt(Lit) is negative, it indicates that the literal is entailed by an empty partial interpretation, so the reason clause is empty
//	if(toInt(ar.getLit())<0){
//		return;
//	}
//
//	lits.push(~ar.getLit());
//
//	const PCSolver& pcsol = *as().getSolver()->getPCSolver();
//	const Lit& head = ar.getAgg().getHead();
//	if(value(head)!=l_Undef && var(ar.getLit())!=var(head)){
//		if(pcsol.assertedBefore(var(head), var(ar.getLit()))){
//			lits.push(value(head)==l_True?~head:head);
//		}
//	}
//
//	Lit comparelit = ar.getLit();
//	if(var(ar.getLit())==var(head)){
//		comparelit = ar.getPropLit();
//	}
//
//	for (vsize i = 0; i < as().getWL().size(); i++) {
//		const WL& wl = as().getWL()[i];
//		if(ar.getExpl()==BASEDONCC){ //Monotone one (one in the set) propagated: take only false monotone ones
//			if(value(wl.getLit())==(ar.getAgg().isUpper()?l_True:l_False)){
//				continue;
//			}
//		}
//		if(ar.getExpl()==BASEDONCP){ //Anti-monotone one (one not in the set) propagated: take only true monotone ones
//			if(value(wl.getLit())==(ar.getAgg().isUpper()?l_False:l_True)){
//				continue;
//			}
//		}
//		if (var(wl.getLit()) != var(comparelit) && value(wl.getLit()) != l_Undef) {
//			if(pcsol.assertedBefore(var(wl.getLit()), var(comparelit))){
//				lits.push(value(wl.getLit())==l_True?~wl.getLit():wl.getLit());
//			}
//		}
//	}
//}
