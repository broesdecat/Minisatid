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

///////
//PW Aggregates
///////

PWAgg::PWAgg(paggs agg) :
	Propagator(agg) {
}

CardPWAgg::CardPWAgg(paggs agg) :
	PWAgg(agg) {
}

rClause CardPWAgg::propagate(const Lit& p, const Watch& w) {
	assert(false);
}

rClause CardPWAgg::propagate(const Agg& agg) {
	assert(false);
	//One part of the watches is no longer necessary until backtrack.
}

void CardPWAgg::backtrack(const Agg& agg) {
	//Set all watches again to the side which was no longer used.
}

void CardPWAgg::getExplanation(vec<Lit>& lits, const AggReason& ar) const {
	assert(false);
}

paggs CardPWAgg::initialize(bool& unsat) {
	if(as().getAgg().size()!=1){
		SumFWAgg* s = new SumFWAgg(asp());
		for (int i = 0; i < as().getAgg().size(); i++) {
			s->as().addAgg(as().getAgg()[i]);
		}
		as().getRefAgg().clear();
		return s->initialize(unsat);
	}
	//TODO handle multiset (not even checked now)
	/*
	 * First find nf and nfex:
	 * go over set, incrementally calc min and max value, by taking positive monotone set literals
	 * and negative anti-monotone ones. If satisfied, nf is finished.
	 * Then go over all in nf, remove them and add extra lits to nfex until satisfied again. Repeat
	 * for all in nf.
	 *
	 * Same for nt and ntex, but switch mono/am and until not-satisfied.
	 */
	pagg agg = as().getAgg()[0];
	int wlsize = as().getWL().size();

	bool headtrue = as().getSolver()->value(agg->getHead())==l_True;
	bool headfalse = as().getSolver()->value(agg->getHead())==l_False;

	if(!headfalse){
		bool nonfalse = isNonFalse(nf.size(), wlsize, agg->getSign(), agg->getBound());
		for(int i=0; i<wlsize; i++){
			WL wl = as().getWL()[i];
			Lit l = isMonotone(*agg, wl)?wl.getLit():~wl.getLit();
			if(!nonfalse){
				nf.push_back(l);
				nonfalse = isNonFalse(nf.size(), wlsize, agg->getSign(), agg->getBound());
			}else{
				nfex.push_back(l);
				break;
			}
		}

		if(nf.size()!=0 && nfex.size()==0 && (headfalse || headtrue)){
			//TODO propagate the set or throw conflict
			//TODO delete?
			return NULL;
		}
	}

	if(!headtrue){
		bool nontrue = isNonTrue(nt.size(), wlsize, agg->getSign(), agg->getBound());
		for(int i=0; i<wlsize; i++){
			WL wl = as().getWL()[i];
			Lit l = !isMonotone(*agg, wl)?wl.getLit():~wl.getLit();
			if(!nontrue){
				nt.push_back(l);
				nontrue = isNonTrue(nt.size(), wlsize, agg->getSign(), agg->getBound());
			}else{
				ntex.push_back(l);
				break;
			}
		}

		if(nt.size()!=0 && ntex.size()==0 && (headfalse || headtrue)){
			//TODO propagate the set or throw conflict
			//TODO delete?
			return NULL;
		}
	}

	for(int i=0; i<nf.size(); i++){
		as().getSolver()->addTempWatch(~nf[i], new Watch(asp(), i, true, true));
	}
	for(int i=0; i<nfex.size(); i++){
		as().getSolver()->addTempWatch(~nfex[i], new Watch(asp(), i, false, true));
	}
	for(int i=0; i<nt.size(); i++){
		as().getSolver()->addTempWatch(~nt[i], new Watch(asp(), i, true, false));
	}
	for(int i=0; i<ntex.size(); i++){
		as().getSolver()->addTempWatch(~ntex[i], new Watch(asp(), i, false, false));
	}

	/*
	 * Necessary methods: issatisfied(min, max, agg), is falsified(min, max, agg)
	 * calcmin(set), calcmax(set)
	 */

	/*
	 * On propagation, do same to fill the sets again.
	 * For all literals in nt/nf for which no replacement can be found, they can be propagated as they
	 * occur in the set.
	 */

	return asp();
}

bool CardPWAgg::isNonFalse(int number, int setsize, Bound sign, Weight bound) const{
	return (sign==LOWERBOUND && number>=setsize-bound) || (sign==UPPERBOUND && number>=bound);
}

bool CardPWAgg::isNonTrue(int number, int setsize, Bound sign, Weight bound) const{
	return (sign==LOWERBOUND && number>bound) || (sign==UPPERBOUND && setsize-bound<number);
}
