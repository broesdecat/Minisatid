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

vwl& CardPWAgg::getSet(watchset w) {
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
	}
}

vwl& CardPWAgg::getWatches(watchset w) {
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
	}
}

bool CardPWAgg::checking(watchset w) const{
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
	}
}

void CardPWAgg::addToWatches(watchset w, int setindex) {
	vwl& set = getSet(w);
	vwl& watches = getWatches(w);
	WL wl = set[setindex];
	watches.push_back(wl);
	set[setindex] = set[set.size() - 1];
	set.pop_back();
	addWatch(wl.getLit(), w, watches.size() - 1);

	/*reportf("In set:  ");
	for(int i=0; i<set.size(); i++){
		gprintLit(set[i].getLit()); reportf(",");
	}
	reportf("\n");

	reportf("Watched: ");
	for(int i=0; i<watches.size(); i++){
		gprintLit(watches[i].getLit()); reportf(",");
	}
	reportf("\n");*/
}

void CardPWAgg::addWatch(const Lit& wl, watchset w, int index) {
	/*reportf("Partial watch added: ");
	gprintLit(wl);
	reportf(" on index %d\n", index);*/
	as().getSolver()->addTempWatch(~wl, new PWatch(asp(), index, w));
}

void CardPWAgg::removeWatches(watchset w){
	vwl& watches = getWatches(w);
	vwl& set = getSet(w);
	vector<vector<pw> >& tempwatches = as().getSolver()->getTempWatches();

	for(int i=0; i<watches.size(); i++){
		vector<pw>& list = tempwatches[toInt(~watches[i].getLit())];
		for(int j=0; j<list.size(); j++){
			PWatch* pw = dynamic_cast<PWatch*> (list[j]);
			if(pw->getIndex()==i && pw->getWatchset()==w){
				list[j] = list[list.size()-1];
				list.pop_back();
				delete pw;
				/*reportf("Partial watch removed: ");
				gprintLit(watches[i].getLit());
				reportf(" on index %d\n", i);*/
				break;
			}
		}

		set.push_back(watches[i]);
	}

	watches.clear();

	/*reportf("In set:  ");
	for(int i=0; i<set.size(); i++){
		gprintLit(set[i].getLit()); reportf(",");
	}
	reportf("\n");

	reportf("Watched: ");
	for(int i=0; i<watches.size(); i++){
		gprintLit(watches[i].getLit()); reportf(",");
	}
	reportf("\n");*/
}

PWAgg::PWAgg(paggs agg) :
	Propagator(agg) {
}

CardPWAgg::CardPWAgg(paggs agg) :
	PWAgg(agg), headvalue(l_Undef), headpropagatedhere(false) {
}

void CardPWAgg::initialize(bool& unsat, bool& sat) {
	// All that we can't handle at the moment is transformed into a fixed watch sum aggregate.
	if (as().getAgg().size() != 1) {
		SumFWAgg* s = new SumFWAgg(asp());
		s->initialize(unsat, sat);
		//reportf("Fully watched propagator used\n");
		return; //FIXME current propagator cannot be deleted!
	}

	const Agg& agg = *as().getAgg()[0];

	//reportf("Partial watched propagator used\n");


	for(int i=0; i<as().getWL().size(); i++){
		const WL& wl = as().getWL()[i];
		const WL& negwl = WL(~wl.getLit(), wl.getWeight());
		setf.push_back(agg.isLower()?negwl:wl);
		sett.push_back(agg.isLower()?wl:negwl);
	}


	bool nffailed = false, ntfailed, nfexfailed = false, ntexfailed = false;
	if (agg.isLower()) {
		//Card(S)<=B
		if (checking(NF)) {
			nffailed = !initializeNFL();
		}
		if (!nffailed && checking(NFEX)) {
			nfexfailed = !initializeEX(NFEX);
		}

		//~Card(S)<=B
		if (checking(NT)) {
			ntfailed = !initializeNTL();
		}
		if (!ntfailed && checking(NTEX)) {
			ntexfailed = !initializeEX(NTEX);
		}
	} else {
		//Card(S)>=B
		if (checking(NF)) {
			nffailed = !initializeNF();
		}
		if (!nffailed && checking(NFEX)) {
			nfexfailed = !initializeEX(NFEX);
		}

		//~Card(S)>=B
		if (checking(NT)) {
			ntfailed = !initializeNT();
		}
		if (!ntfailed && checking(NTEX)) {
			ntexfailed = !initializeEX(NTEX);
		}
	}

	rClause confl = nullPtrClause;
	if (nffailed) {
		confl = as().getSolver()->notifySolver(~agg.getHead(), new AggReason( agg, ~agg.getHead(), BASEDONCC, false));
		if (confl != nullPtrClause) {
			unsat = true;
		}else{
			sat = true;
		}
		return;
	}
	if (ntfailed) {
		confl = as().getSolver()->notifySolver(agg.getHead(), new AggReason( agg, agg.getHead(), BASEDONCC, false));
		if (confl != nullPtrClause) {
			unsat = true;
			return;
		}else{
			sat = true;
		}
		return;
	}

	if (ntexfailed) {
		for (vsize i = 0; confl != nullPtrClause && i < nt.size(); i++) {
			confl = as().getSolver()->notifySolver(nt[i].getLit(), new AggReason(agg, nt[i].getLit(), BASEDONCC, false));
		}
		if (confl != nullPtrClause) {
			unsat = true;
		} else {
			sat = true;
		}
		return;
	}
	if (nfexfailed) {
		rClause confl = nullPtrClause;
		for (vsize i = 0; confl != nullPtrClause && i < nf.size(); i++) {
			confl = as().getSolver()->notifySolver(nf[i].getLit(), new AggReason(agg, nf[i].getLit(), BASEDONCC, false));
		}
		if (confl != nullPtrClause) {
			unsat = true;
		} else {
			sat = true;
		}
		return;
	}

	PWAgg::initialize(unsat, sat);
}

bool CardPWAgg::initializeNF() {
	const Agg& agg = *as().getAgg()[0];
	vwl& set = getSet(NF);
	for (vsize i = 0; i < set.size(); i++) {
		const WL& wl = set[i];
		if (Weight(nf.size()) < agg.getBound() && value(wl.getLit()) != l_False) {
			addToWatches(NF, i);
			i--;
		}
	}
	return Weight(nf.size()) >= agg.getBound();
}

bool CardPWAgg::initializeNT() {
	const Agg& agg = *as().getAgg()[0];
	vwl& set = getSet(NT);
	for (vsize i = 0; i < set.size(); i++) {
		const WL& wl = set[i];
		if (Weight(nt.size()) <= Weight(as().getWL().size()) - agg.getBound() && value(wl.getLit()) != l_True) {
			addToWatches(NT, i);
			i--;
		}
	}
	return Weight(nt.size()) > Weight(as().getWL().size()) - agg.getBound();
}

bool CardPWAgg::initializeNTL() {
	const Agg& agg = *as().getAgg()[0];
	vwl& set = getSet(NT);
	for (vsize i = 0; i < set.size(); i++) {
		const WL& wl = set[i];
		if (Weight(nt.size()) <= agg.getBound() && value(wl.getLit()) != l_False) {
			addToWatches(NT, i);
			i--;
		}
	}
	return Weight(nt.size()) > agg.getBound();
}

bool CardPWAgg::initializeNFL() {
	const Agg& agg = *as().getAgg()[0];
	vwl& set = getSet(NF);
	for (vsize i = 0; i < set.size(); i++) {
		const WL& wl = set[i];
		if (Weight(nf.size()) < Weight(as().getWL().size()) - agg.getBound() && value(wl.getLit()) != l_True) {
			addToWatches(NF, i);
			i--;
		}
	}
	return Weight(nf.size()) >= Weight(as().getWL().size()) - agg.getBound();
}

bool CardPWAgg::initializeEX(watchset w) {
	bool found = false;
	vwl& set = getSet(w);
	for (vsize i = 0; !found && i < set.size(); i++) {
		WL wl = set[i];
		if (value(wl.getLit()) != l_False) {
			addToWatches(w, i);
			i--;
			found = true;
		}
	}
	return found;
}

bool CardPWAgg::replace(vsize index, watchset w) {
	bool found = false;
	vwl& set = getSet(w);
	vwl& watches = getWatches(w);

	for (vsize i = 0; !found && i < set.size(); i++) {
		WL wl = set[i];
		if (value(wl.getLit()) != l_False) {
			set[i] = watches[index];
			watches[index] = wl;
			addWatch(wl.getLit(), w, index);
			found = true;
		}
	}
	return found;
}

rClause CardPWAgg::propagate(const Lit& p, const Watch& watch) {
	rClause confl = nullPtrClause;

	PWatch const * pw = dynamic_cast<PWatch const *> (&watch);
	const PWatch& w = *pw;

	/*reportf("Partial watch propagated: ");
	gprintLit(p);
	reportf(" on index %d\n", w.getIndex());*/

	bool found = true;
	if (isF(w.getWatchset())) {
		if (!isEX(w.getWatchset())) { //non-ex
			found = replace(w.getIndex(), NF);
		} else if (isEX(w.getWatchset())) { //nf ex
			found = replace(w.getIndex(), NFEX);
		}
	} else {
		if (!isEX(w.getWatchset())) { //non-ex
			found = replace(w.getIndex(), NT);
		} else if (isEX(w.getWatchset())) { //nf ex
			found = replace(w.getIndex(), NTEX);
		}
	}

	/*reportf("Current partial watches: \n");
	watchset wt = NF;
	for (int i = 0; i < getWatches(wt).size(); i++) {
		if(checking(NF)){
			reportf("    NF    ");
			gprintLit(getWatches(wt)[i].getLit());
			reportf("\n");
		}
	}
	wt = NFEX;
	for (int i = 0; i < getWatches(wt).size(); i++) {
		if(checking(NFEX)){
			reportf("    NFEX ");
			gprintLit(getWatches(wt)[i].getLit());
			reportf("\n");
		}
	}
	wt = NT;
	for (int i = 0; i < getWatches(wt).size(); i++) {
		if(checking(NT)){
			reportf("    NT   ");
			gprintLit(getWatches(wt)[i].getLit());
			reportf("\n");
		}
	}
	wt = NTEX;
	for (int i = 0; i < getWatches(wt).size(); i++) {
		if(checking(NTEX)){
			reportf("    NTEX ");
			gprintLit(getWatches(wt)[i].getLit());
			reportf("\n");
		}
	}*/

	if (!found) {
		if (checking(NFEX)) {
			// propagate all others in NF and propagate NFex
			for (vsize i = 0; confl == nullPtrClause && i < nf.size(); i++) {
				if (i == w.getIndex() && !isEX(w.getWatchset())) {
					continue;
				}
				confl = as().getSolver()->notifySolver(nf[i].getLit(), new AggReason(*as().getAgg()[0], nf[i].getLit(), BASEDONCC, false));
			}
			if (confl == nullPtrClause) {
				for (vsize i = 0; confl == nullPtrClause && i < nfex.size(); i++) {
					if (i == w.getIndex() && isEX(w.getWatchset())) {
						continue;
					}
					confl = as().getSolver()->notifySolver(nfex[i].getLit(), new AggReason(*as().getAgg()[0], nfex[i].getLit(), BASEDONCC, false));
				}
			}
		} else if (isF(w.getWatchset()) && checking(NF)) {
			//propagate head false
			Lit l = ~as().getAgg()[0]->getHead();
			confl = as().getSolver()->notifySolver(l, new AggReason( *as().getAgg()[0], l, BASEDONCC, false));
			if(confl==nullPtrClause){
				headpropagatedhere = true;
			}
		} else if (checking(NTEX)) {
			// propagate all others in NF and propagate NFex
			for (vsize i = 0; confl == nullPtrClause && i < nt.size(); i++) {
				if (i == w.getIndex() && !isEX(w.getWatchset())) {
					continue;
				}
				confl = as().getSolver()->notifySolver(nt[i].getLit(), new AggReason(*as().getAgg()[0], nt[i].getLit(), BASEDONCC, false));
			}
			if (confl == nullPtrClause) {
				for (vsize i = 0; confl == nullPtrClause && i < ntex.size(); i++) {
					if (i == w.getIndex() && isEX(w.getWatchset())) {
						continue;
					}
					confl = as().getSolver()->notifySolver(ntex[i].getLit(), new AggReason(*as().getAgg()[0], ntex[i].getLit(), BASEDONCC, false));
				}
			}
		} else if (!isF(w.getWatchset()) && checking(NT)) {
			//propagate head true
			Lit l = as().getAgg()[0]->getHead();
			confl = as().getSolver()->notifySolver(l, new AggReason( *as().getAgg()[0], l, BASEDONCC, false));
			if(confl==nullPtrClause){
				headpropagatedhere = true;
			}
		}
		//TODO do something about sign confusion
		addWatch(~p, w.getWatchset(), w.getIndex());
		return confl;
	}

	return nullPtrClause;
}

//TODO should not add head as watch in nf(ex) or ~head as watch in nt(ex)

rClause CardPWAgg::propagate(const Agg& agg) {
	if(headpropagatedhere){
		//TODO deze check zou niet noodzakelijk mogen zijn voor de correctheid, maar is dat nu wel. Probleem is
		//dat hij soms bij head propageren geen extension vindt en dan alles propageert, maar eigenlijk
		//hoeft dat niet als een volledig true conflict set gevonden kan worden
		return nullPtrClause;
	}
	//reportf("PROPAGATED HEAD\n");

	headvalue = value(agg.getHead());

	rClause confl = nullPtrClause;

	assert(nfex.size() == 0 && ntex.size() == 0);

	if(!checking(NF)){
		removeWatches(NF);
	}

	if(!checking(NT)){
		removeWatches(NT);
	}

	if (checking(NFEX)) {
		if (!initializeEX(NFEX)) {
			for (vsize i = 0; confl == nullPtrClause && i < nf.size(); i++) {
				confl = as().getSolver()->notifySolver(nf[i].getLit(), new AggReason(*as().getAgg()[0], nf[i].getLit(), BASEDONCC, false));
			}
		}
	}

	if (checking(NTEX)) {
		if (!initializeEX(NTEX)) {
			for (vsize i = 0; confl == nullPtrClause && i < nt.size(); i++) {
				confl = as().getSolver()->notifySolver(nt[i].getLit(), new AggReason(*as().getAgg()[0], nt[i].getLit(), BASEDONCC, false));
			}
		}
	}

	return confl;
}

void CardPWAgg::backtrack(const Agg& agg) {
	//reportf("BACKTRACKED HEAD\n");
	headpropagatedhere = false;

	if (checking(NFEX)) {
		removeWatches(NFEX);
	}

	if (checking(NTEX)) {
		removeWatches(NTEX);
	}

	headvalue = l_Undef;

	if(checking(NF)){
		if(agg.isLower()){
			initializeNFL();
		}else{
			initializeNF();
		}
	}

	if(checking(NT)){
		if(agg.isLower()){
			initializeNTL();
		}else{
			initializeNT();
		}
	}
}

void CardPWAgg::getExplanation(vec<Lit>& lits, const AggReason& ar) const {
	const Lit& head = as().getAgg()[0]->getHead();
	if(value(head)!=l_Undef && var(ar.getLit())!=var(head)){
		bool add = true;
		if(as().getSolver()->getPCSolver()->getLevel(var(head))	!= as().getSolver()->getPCSolver()->getLevel(var(ar.getLit()))){
			const vl& trail = as().getSolver()->getPCSolver()->getRecentAssignments();

			bool before = false;
			for (int i = 0; i < trail.size(); i++) {
				if (var(trail[i]) == var(ar.getLit())) {
					add = false;
					break;
				}
				if (var(trail[i]) == var(head)) {
					break;
				}
			}
		}
		if(add){
			lits.push(value(head)==l_True?~head:head);
		}
	}

	for (vsize i = 0; i < as().getWL().size(); i++) {
		const WL& wl = as().getWL()[i];
		if (var(wl.getLit()) != var(ar.getLit()) && value(wl.getLit()) != l_Undef) {
			bool add = true;
			if (as().getSolver()->getPCSolver()->getLevel(var(wl.getLit()))	== as().getSolver()->getPCSolver()->getLevel(var(ar.getLit()))) {
				const vl& trail = as().getSolver()->getPCSolver()->getRecentAssignments();

				for (int i = 0; i < trail.size(); i++) {
					if (var(trail[i]) == var(ar.getLit())) {
						add = false;
						break;
					}
					if (var(trail[i]) == var(wl.getLit())) {
						break;
					}
				}
			}

			if(add){
				lits.push(value(wl.getLit())==l_True?~wl.getLit():wl.getLit());
			}
		}
	}
}
