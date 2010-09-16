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

PWAgg::PWAgg(paggs agg) :
	Propagator(agg) {
}

CardPWAgg::CardPWAgg(paggs agg): PWAgg(agg), headvalue(l_Undef){
}

void CardPWAgg::initialize	(bool& unsat, bool& sat){
	headvalue = value(as().getAgg()[0]->getHead());

	// All that we can't handle at the moment is transformed into a fixed watch sum aggregate.
	if(as().getAgg().size()!=1 || as().getAgg()[0]->isLower() || headvalue==l_Undef){
		SumFWAgg* s = new SumFWAgg(asp());
		s->initialize(unsat, sat);
		reportf("Fully watched propagator used\n");
		return; //FIXME current propagator cannot be deleted!
	}

	reportf("Partially watched propagator used\n");

	const Agg& agg = *as().getAgg()[0];

	//Card(S)>=B
	if(checkingNF()){
		if(!initializeNF()){
			unsat = true; return;
		}
	}
	if(checkingNFex()){
		if(!initializeNFex()){
			rClause confl = nullPtrClause;
			for(vsize i=0; confl!=nullPtrClause && i<nf.size(); i++){
				confl = as().getSolver()->notifySolver(nf[i].getLit(), new AggReason(agg, nf[i].getLit(), BASEDONCC, false));
			}
			if(confl!=nullPtrClause){
				unsat = true;
			}else{
				sat = true;
			}
			return;
		}
	}

	//~Card(S)>=B
	if(checkingNT()){
		if(!initializeNT()){
			unsat = true; return;
		}
	}
	if(checkingNTex()){
		if(!initializeNTex()){
			rClause confl = nullPtrClause;
			for(vsize i=0; confl!=nullPtrClause && i<nt.size(); i++){
				confl = as().getSolver()->notifySolver(nt[i].getLit(), new AggReason(agg, nt[i].getLit(), BASEDONCC, false));
			}
			if(confl!=nullPtrClause){
				unsat = true;
			}else{
				sat = true;
			}
			return;
		}
	}

	if(checkingNF()){
		addWatches(nf, true, false);
	}
	if(checkingNFex()){
		addWatches(nfex, true, true);
	}
	if(checkingNT()){
		addWatches(nt, false, false);
	}
	if(checkingNTex()){
		addWatches(ntex, false, true);
	}

	PWAgg::initialize(unsat, sat);
}

void CardPWAgg::addWatches(const vector<WL>& set, bool nf, bool ex) const{
	for(vsize i=0; i<set.size(); i++){
		reportf("Partial watch added: "); gprintLit(set[i].getLit()); reportf("\n");
		as().getSolver()->addTempWatch(~set[i].getLit(), new Watch(asp(), i, nf, !ex));
	}
}

bool CardPWAgg::initializeNF(){
	const Agg& agg = *as().getAgg()[0];
	const vwl& set = as().getWL();
	for(vsize i=0; i<set.size(); i++){
		const WL& wl = set[i];
		if(Weight(nf.size())>=agg.getBound()){
			setf.push_back(wl);
		}else{
			if(value(wl.getLit())==l_False){
				setf.push_back(wl);
			}else{
				nf.push_back(wl);
			}
		}
	}
	return Weight(nf.size())>=agg.getBound();
}

bool CardPWAgg::initializeNFex(){
	bool found = false;
	for(vsize i=0; !found && i<setf.size(); i++){
		WL wl = setf[i];
		if(value(wl.getLit())!=l_False){
			nfex.push_back(wl);
			setf[i] = setf[setf.size()-1];
			setf.pop_back();
			found = true;
		}
	}
	return found;
}

bool CardPWAgg::initializeNT(){
	const Agg& agg = *as().getAgg()[0];
	const vwl& set = as().getWL();
	for(vsize i=0; i<set.size(); i++){
		const WL& t = set[i];
		WL wl = WL(~t.getLit(), t.getWeight());
		if(Weight(nt.size())>Weight(set.size())-agg.getBound()){
			sett.push_back(wl);
		}else{
			if(value(wl.getLit())==l_True){
				sett.push_back(wl);
			}else{
				nt.push_back(wl);
			}
		}
	}
	return Weight(nt.size())>Weight(set.size())-agg.getBound();
}

bool CardPWAgg::initializeNTex(){
	bool found = false;
	for(vsize i=0; !found && i<sett.size(); i++){
		WL wl = sett[i];
		if(value(wl.getLit())!=l_False){
			ntex.push_back(wl);
			sett[i] = sett[sett.size()-1];
			sett.pop_back();
			found = true;
		}
	}
	return found;
}

bool CardPWAgg::replaceNF(vsize index){
	bool found = false;
	for(vsize i=0; !found && i<setf.size(); i++){
		WL wl = setf[i];
		if(value(wl.getLit())!=l_False){
			setf[i] = nf[index];
			nf[index] = wl;
			reportf("Partial watch added: "); gprintLit(wl.getLit()); reportf("\n");
			as().getSolver()->addTempWatch(~wl.getLit(), new Watch(asp(), index, true, true));
			found = true;
		}
	}
	return found;
}

bool CardPWAgg::replaceNFex(vsize index){
	bool found = false;
	for(vsize i=0; !found && i<setf.size(); i++){
		WL wl = setf[i];
		if(value(wl.getLit())!=l_False){
			setf[i] = nfex[index];
			nfex[index] = wl;
			reportf("Partial watch added: "); gprintLit(wl.getLit()); reportf("\n");
			as().getSolver()->addTempWatch(~wl.getLit(), new Watch(asp(), index, true, false));
			found = true;
		}
	}
	return found;
}

bool CardPWAgg::replaceNT(vsize index){
	bool found = false;
	for(vsize i=0; !found && i<sett.size(); i++){
		WL wl = sett[i];
		if(value(wl.getLit())!=l_False){
			sett[i] = nt[index];
			nt[index] = wl;
			reportf("Partial watch added: "); gprintLit(wl.getLit()); reportf("\n");
			as().getSolver()->addTempWatch(~wl.getLit(), new Watch(asp(), index, false, true));
			found = true;
		}
	}
	return found;
}

bool CardPWAgg::replaceNTex(vsize index){
	bool found = false;
	for(vsize i=0; !found && i<sett.size(); i++){
		WL wl = sett[i];
		if(value(wl.getLit())!=l_False){
			sett[i] = ntex[index];
			ntex[index] = wl;
			reportf("Partial watch added: "); gprintLit(wl.getLit()); reportf("\n");
			as().getSolver()->addTempWatch(~wl.getLit(), new Watch(asp(), index, false, false));
			found = true;
		}
	}
	return found;
}

rClause CardPWAgg::propagate(const Lit& p, const Watch& w){
	rClause confl = nullPtrClause;

	reportf("Partial watch propagated\n");

	bool found = false;
	if(w.isSetLit()){
		if(w.isPos() && checkingNF()){ //non-ex
			found = replaceNF(w.getIndex());
		}else if(!w.isPos() && checkingNFex()){ //nf ex
			found = replaceNFex(w.getIndex());
		}
	}else{
		if(w.isPos() && checkingNT()){ //non-ex
			found = replaceNT(w.getIndex());
		}else if(!w.isPos() && checkingNTex()){ //nf ex
			found = replaceNTex(w.getIndex());
		}
	}

	/*reportf("Current partial watches: \n");
	for(int i=0; i<nf.size(); i++){
		reportf("    "); gprintLit(nf[i].getLit()); reportf("\n");
	}
	for(int i=0; i<nfex.size(); i++){
		reportf("    "); gprintLit(nfex[i].getLit()); reportf("\n");
	}
	for(int i=0; i<nt.size(); i++){
		reportf("    "); gprintLit(nt[i].getLit()); reportf("\n");
	}
	for(int i=0; i<ntex.size(); i++){
		reportf("    "); gprintLit(ntex[i].getLit()); reportf("\n");
	}*/

	if(!found){
		if(checkingNFex()){
			// propagate all others in NF and propagate NFex
			for(vsize i=0; confl==nullPtrClause && i<nf.size(); i++){
				if(i==w.getIndex()){
					continue;
				}
				confl = as().getSolver()->notifySolver(nf[i].getLit(), new AggReason(*as().getAgg()[0], nf[i].getLit(), BASEDONCC, false));
			}
			if(confl==nullPtrClause){
				for(vsize i=0; confl==nullPtrClause && i<nfex.size(); i++){
					confl = as().getSolver()->notifySolver(nfex[i].getLit(), new AggReason(*as().getAgg()[0], nfex[i].getLit(), BASEDONCC, false));
				}
			}
			as().getSolver()->addTempWatch(p, new Watch(w.getAggComb(), w.getIndex(), w.isSetLit(), w.isPos()));
			return confl;
		}else if(checkingNF()){
			//propagate head true
			Lit l = as().getAgg()[0]->getHead();
			confl = as().getSolver()->notifySolver(l, new AggReason(*as().getAgg()[0], l, BASEDONCC, false));
			as().getSolver()->addTempWatch(p, new Watch(w.getAggComb(), w.getIndex(), w.isSetLit(), w.isPos()));
			return confl;
		}else if(checkingNTex()){
			// propagate all others in NF and propagate NFex
			for(vsize i=0; confl==nullPtrClause && i<nt.size(); i++){
				if(i==w.getIndex()){
					continue;
				}
				confl = as().getSolver()->notifySolver(nt[i].getLit(), new AggReason(*as().getAgg()[0], nt[i].getLit(), BASEDONCC, false));
			}
			if(confl==nullPtrClause){
				for(vsize i=0; confl==nullPtrClause && i<ntex.size(); i++){
					confl = as().getSolver()->notifySolver(ntex[i].getLit(), new AggReason(*as().getAgg()[0], ntex[i].getLit(), BASEDONCC, false));
				}
			}
			as().getSolver()->addTempWatch(p, new Watch(w.getAggComb(), w.getIndex(), w.isSetLit(), w.isPos()));
			return confl;
		}else if(checkingNT()){
			//propagate head true
			Lit l = as().getAgg()[0]->getHead();
			confl = as().getSolver()->notifySolver(~l, new AggReason(*as().getAgg()[0], ~l, BASEDONCC, false));
			as().getSolver()->addTempWatch(p, new Watch(w.getAggComb(), w.getIndex(), w.isSetLit(), w.isPos()));
			return confl;
		}
	}


	return nullPtrClause;
}

rClause CardPWAgg::propagate(const Agg& agg){
	reportf("PROPAGATED HEAD\n");
	headvalue = value(agg.getHead());

	return nullPtrClause;
}

void CardPWAgg::backtrack(const Agg& agg){
	reportf("BACKTRACKED HEAD\n");
	headvalue = l_Undef;
}

void CardPWAgg::getExplanation(vec<Lit>& lits, const AggReason& ar) const{
	for(vsize i=0; i<as().getWL().size(); i++){
		const WL& wl = as().getWL()[i];
		if(var(wl.getLit())!=var(ar.getLit()) && value(wl.getLit())!=l_Undef){
			lits.push(~wl.getLit());
		}
	}
}
