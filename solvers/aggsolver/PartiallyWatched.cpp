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

CardPWAgg::CardPWAgg(paggs agg):
			PWAgg(agg){
}

void CardPWAgg::initialize	(bool& unsat, bool& sat){
	// All that we can't handle at the moment is transformed into a fixed watch sum aggregate.
	if(as().getAgg().size()!=1 || as().getAgg()[0]->isLower() || as().getSolver()->value(as().getAgg()[0]->getHead())!=l_True){
		SumFWAgg* s = new SumFWAgg(asp());
		s->initialize(unsat, sat);
		reportf("Fully watched propagator used\n");
		return; //FIXME current propagator cannot be deleted!
	}

	reportf("Partially watched propagator used\n");

	const Agg& agg = *as().getAgg()[0];
	const vwl& set = as().getWL();

	//Card(S)>=B
	for(int i=0; i<set.size(); i++){
		const WL& wl = set[i];
		if(nf.size()>agg.getBound()){
			setf.push_back(wl);
		}else{
			if(as().getSolver()->value(wl.getLit())==l_False){
				setf.push_back(wl);
			}else{
				nf.push_back(wl);
			}
		}
	}

	if(nf.size()<=agg.getBound()){
		if(nf.size()<agg.getBound()){
			unsat = true;
			return;
		}else{
			rClause confl = nullPtrClause;
			for(int i=0; confl!=nullPtrClause && i<nf.size(); i++){
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

	for(int i=0; i<nf.size(); i++){
		reportf("Partial watch added: "); gprintLit(nf[i].getLit()); reportf("\n");
		as().getSolver()->addTempWatch(~nf[i].getLit(), new Watch(asp(), i, true, true));
	}
}

rClause CardPWAgg::propagate(const Lit& p, const Watch& w){
	reportf("Partial watch propagated\n");
	bool found = false;
	for(int i=0; !found && i<setf.size(); i++){
		WL wl = setf[i];
		if(as().getSolver()->value(wl.getLit())!=l_False){
			setf[i] = nf[w.getIndex()];
			nf[w.getIndex()] = wl;
			reportf("Partial watch added: "); gprintLit(wl.getLit()); reportf("\n");
			as().getSolver()->addTempWatch(~wl.getLit(), new Watch(asp(), w.getIndex(), true, true));
			found = true;
		}
	}

	if(!found){
		rClause confl = nullPtrClause;
		for(int i=0; confl==nullPtrClause && i<nf.size(); i++){
			if(i==w.getIndex()){
				continue;
			}
			confl = as().getSolver()->notifySolver(nf[i].getLit(), new AggReason(*as().getAgg()[0], nf[i].getLit(), BASEDONCC, false));
		}
		return confl;
	}
	return nullPtrClause;
}

rClause CardPWAgg::propagate(const Agg& agg){
	assert(false);
};

void CardPWAgg::backtrack(const Agg& agg){
	assert(false);
}

void CardPWAgg::getExplanation(vec<Lit>& lits, const AggReason& ar) const{
	for(int i=0; i<as().getWL().size(); i++){
		const WL& wl = as().getWL()[i];
		if(var(wl.getLit())!=var(ar.getLit()) && as().getSolver()->value(wl.getLit())!=l_Undef){
			lits.push(~wl.getLit());
		}
	}
};
