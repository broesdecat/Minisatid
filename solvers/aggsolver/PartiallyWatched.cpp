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

vector<bool>& CardPWAgg::getBoolWatches(watchset w) {
	switch (w) {
	case NF:
		return nfb;
		break;
	case NT:
		return ntb;
		break;
	case NFEX:
		return nfexb;
		break;
	case NTEX:
		return ntexb;
		break;
	}
}

void CardPWAgg::addToWatches(const WL& wl, watchset w) {
	vwl& watches = getWatches(w);
	watches.push_back(wl);
	getBoolWatches(w).push_back(false);
	addWatch(wl.getLit(), w, watches.size() - 1);
}

void CardPWAgg::addToWatches(watchset w, int setindex) {
	vwl& set = getSet(w);
	vwl& watches = getWatches(w);
	WL wl = set[setindex];
	watches.push_back(wl);
	set[setindex] = set[set.size() - 1];
	set.pop_back();
	getBoolWatches(w).push_back(false);
	addWatch(wl.getLit(), w, watches.size() - 1);
}

void CardPWAgg::addWatch(const Lit& wl, watchset w, int index) {
	if(getBoolWatches(w)[index]!=true){
		reportf("Partial watch added: ");
		gprintLit(wl);
		reportf(" on index %d\n", index);
		as().getSolver()->addTempWatch(~wl, new PWatch(asp(), index, w));
		getBoolWatches(w)[index] = true;
	}
}

void CardPWAgg::removeWatch(const PWatch& w) {
	getBoolWatches(w.getWatchset())[w.getIndex()] = false;
}

void CardPWAgg::removeFromWatches(watchset w, int watchindex) {

}

void CardPWAgg::watchRemoved(watchset w, int watchindex) {

}

PWAgg::PWAgg(paggs agg) :
	Propagator(agg) {
}

CardPWAgg::CardPWAgg(paggs agg) :
	PWAgg(agg), headvalue(l_Undef) {
}

void CardPWAgg::initialize(bool& unsat, bool& sat) {
	// All that we can't handle at the moment is transformed into a fixed watch sum aggregate.
	if (as().getAgg().size() != 1 /*|| value(as().getAgg()[0]->getHead())==l_Undef*/) {
		SumFWAgg* s = new SumFWAgg(asp());
		s->initialize(unsat, sat);
		reportf("Fully watched propagator used\n");
		return; //FIXME current propagator cannot be deleted!
	}

	const Agg& agg = *as().getAgg()[0];

	reportf("Partial watched propagator used\n");

	bool nffailed = false, ntfailed, nfexfailed = false, ntexfailed = false;
	if (agg.isLower()) {
		//Card(S)<=B
		if (checkingNF()) {
			nffailed = !initializeNFL();
		}
		if (!nffailed && checkingNFex()) {
			nfexfailed = !initializeEX(NFEX);
		}

		//~Card(S)<=B
		if (checkingNT()) {
			ntfailed = !initializeNTL();
		}
		if (!ntfailed && checkingNTex()) {
			ntexfailed = !initializeEX(NTEX);
		}
	} else {
		//Card(S)>=B
		if (checkingNF()) {
			nffailed = !initializeNF();
		}
		if (!nffailed && checkingNFex()) {
			nfexfailed = !initializeEX(NFEX);
		}

		//~Card(S)>=B
		if (checkingNT()) {
			ntfailed = !initializeNT();
		}
		if (!ntfailed && checkingNTex()) {
			ntexfailed = !initializeEX(NTEX);
		}
	}

	rClause confl = nullPtrClause;
	if (nffailed) {
		confl = as().getSolver()->notifySolver(~agg.getHead(), new AggReason(
				agg, ~agg.getHead(), BASEDONCC, false));
		if (confl != nullPtrClause) {
			unsat = true;
			return;
		}
	}
	if (ntfailed) {
		confl = as().getSolver()->notifySolver(agg.getHead(), new AggReason(
				agg, agg.getHead(), BASEDONCC, false));
		if (confl != nullPtrClause) {
			unsat = true;
			return;
		}
	}

	if (ntexfailed) {
		for (vsize i = 0; confl != nullPtrClause && i < nt.size(); i++) {
			confl = as().getSolver()->notifySolver(nt[i].getLit(),
					new AggReason(agg, nt[i].getLit(), BASEDONCC, false));
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
			confl = as().getSolver()->notifySolver(nf[i].getLit(),
					new AggReason(agg, nf[i].getLit(), BASEDONCC, false));
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
	const vwl& set = as().getWL();
	for (vsize i = 0; i < set.size(); i++) {
		const WL& wl = set[i];
		if (Weight(nf.size()) >= agg.getBound()) {
			setf.push_back(wl);
		} else {
			if (value(wl.getLit()) == l_False) {
				setf.push_back(wl);
			} else {
				addToWatches(wl, NF);
			}
		}
	}
	return Weight(nf.size()) >= agg.getBound();
}

bool CardPWAgg::initializeNT() {
	const Agg& agg = *as().getAgg()[0];
	const vwl& set = as().getWL();
	for (vsize i = 0; i < set.size(); i++) {
		const WL& t = set[i];
		WL wl = WL(~t.getLit(), t.getWeight());
		if (Weight(nt.size()) > Weight(set.size()) - agg.getBound()) {
			sett.push_back(wl);
		} else {
			if (value(wl.getLit()) == l_True) {
				sett.push_back(wl);
			} else {
				addToWatches(wl, NT);
			}
		}
	}
	return Weight(nt.size()) > Weight(set.size()) - agg.getBound();
}

bool CardPWAgg::initializeNTL() {
	const Agg& agg = *as().getAgg()[0];
	const vwl& set = as().getWL();
	for (vsize i = 0; i < set.size(); i++) {
		const WL& wl = set[i];
		if (Weight(nt.size()) > agg.getBound()) {
			sett.push_back(wl);
		} else {
			if (value(wl.getLit()) == l_False) {
				sett.push_back(wl);
			} else {
				addToWatches(wl, NT);
			}
		}
	}
	return Weight(nt.size()) > agg.getBound();
}

bool CardPWAgg::initializeNFL() {
	const Agg& agg = *as().getAgg()[0];
	const vwl& set = as().getWL();
	for (vsize i = 0; i < set.size(); i++) {
		const WL& t = set[i];
		WL wl = WL(~t.getLit(), t.getWeight());
		if (Weight(nf.size()) >= Weight(set.size()) - agg.getBound()) {
			setf.push_back(wl);
		} else {
			if (value(wl.getLit()) == l_True) {
				setf.push_back(wl);
			} else {
				addToWatches(wl, NF);
			}
		}
	}
	return Weight(nf.size()) >= Weight(set.size()) - agg.getBound();
}

bool CardPWAgg::initializeEX(watchset w) {
	bool found = false;
	vwl& set = getSet(w);
	for (vsize i = 0; !found && i < set.size(); i++) {
		WL wl = set[i];
		if (value(wl.getLit()) != l_False) {
			addToWatches(w, i);
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

	reportf("Partial watch propagated: ");
	gprintLit(p);
	reportf(" on index %d\n", w.getIndex());
	removeWatch(w);

	bool found = true;
	if (isF(w.getWatchset())) {
		if (!isEX(w.getWatchset()) && nf[w.getIndex()].getLit() == ~p
				&& checkingNF()) { //non-ex
			found = replace(w.getIndex(), NF);
		} else if (isEX(w.getWatchset()) && nfex[w.getIndex()].getLit() == ~p
				&& checkingNFex()) { //nf ex
			found = replace(w.getIndex(), NFEX);
		}
	} else {
		if (!isEX(w.getWatchset()) && nt[w.getIndex()].getLit() == ~p
				&& checkingNT()) { //non-ex
			found = replace(w.getIndex(), NT);
		} else if (isEX(w.getWatchset()) && ntex[w.getIndex()].getLit() == ~p
				&& checkingNTex()) { //nf ex
			found = replace(w.getIndex(), NTEX);
		}
	}

	reportf("Current partial watches: \n");
	for (int i = 0; i < nf.size(); i++) {
		reportf("    ");
		gprintLit(nf[i].getLit());
		reportf("\n");
	}
	for (int i = 0; i < nfex.size(); i++) {
		reportf("    ");
		gprintLit(nfex[i].getLit());
		reportf("\n");
	}
	for (int i = 0; i < nt.size(); i++) {
		reportf("    ");
		gprintLit(nt[i].getLit());
		reportf("\n");
	}
	for (int i = 0; i < ntex.size(); i++) {
		reportf("    ");
		gprintLit(ntex[i].getLit());
		reportf("\n");
	}

	if (!found) {
		if (checkingNFex()) {
			// propagate all others in NF and propagate NFex
			for (vsize i = 0; confl == nullPtrClause && i < nf.size(); i++) {
				if (i == w.getIndex() && !isEX(w.getWatchset())) {
					continue;
				}
				confl = as().getSolver()->notifySolver(nf[i].getLit(),
						new AggReason(*as().getAgg()[0], nf[i].getLit(),
								BASEDONCC, false));
			}
			if (confl == nullPtrClause) {
				for (vsize i = 0; confl == nullPtrClause && i < nfex.size(); i++) {
					if (i == w.getIndex() && isEX(w.getWatchset())) {
						continue;
					}
					confl = as().getSolver()->notifySolver(nfex[i].getLit(),
							new AggReason(*as().getAgg()[0], nfex[i].getLit(),
									BASEDONCC, false));
				}
			}
		} else if (checkingNF()) {
			//propagate head true
			Lit l = as().getAgg()[0]->getHead();
			confl = as().getSolver()->notifySolver(l, new AggReason(
					*as().getAgg()[0], l, BASEDONCC, false));
		} else if (checkingNTex()) {
			// propagate all others in NF and propagate NFex
			for (vsize i = 0; confl == nullPtrClause && i < nt.size(); i++) {
				if (i == w.getIndex() && !isEX(w.getWatchset())) {
					continue;
				}
				confl = as().getSolver()->notifySolver(nt[i].getLit(),
						new AggReason(*as().getAgg()[0], nt[i].getLit(),
								BASEDONCC, false));
			}
			if (confl == nullPtrClause) {
				for (vsize i = 0; confl == nullPtrClause && i < ntex.size(); i++) {
					if (i == w.getIndex() && isEX(w.getWatchset())) {
						continue;
					}
					confl = as().getSolver()->notifySolver(ntex[i].getLit(),
							new AggReason(*as().getAgg()[0], ntex[i].getLit(),
									BASEDONCC, false));
				}
			}
		} else if (checkingNT()) {
			//propagate head false
			Lit l = as().getAgg()[0]->getHead();
			confl = as().getSolver()->notifySolver(~l, new AggReason(
					*as().getAgg()[0], ~l, BASEDONCC, false));
		}
		//TODO do something about sign confusion
		addWatch(~p, w.getWatchset(), w.getIndex());
		return confl;
	}

	return nullPtrClause;
}

rClause CardPWAgg::propagate(const Agg& agg) {
	reportf("PROPAGATED HEAD\n");
	headvalue = value(agg.getHead());

	rClause confl = nullPtrClause;

	assert(nfex.size() == 0 && ntex.size() == 0);

	if (checkingNFex()) {
		if (!initializeEX(NFEX)) {
			for (vsize i = 0; confl == nullPtrClause && i < nf.size(); i++) {
				confl = as().getSolver()->notifySolver(nf[i].getLit(),
						new AggReason(*as().getAgg()[0], nf[i].getLit(),
								BASEDONCC, false));
			}
		}
	}

	if (checkingNTex()) {
		if (!initializeEX(NTEX)) {
			for (vsize i = 0; confl == nullPtrClause && i < nt.size(); i++) {
				confl = as().getSolver()->notifySolver(nt[i].getLit(),
						new AggReason(*as().getAgg()[0], nt[i].getLit(),
								BASEDONCC, false));
			}
		}
	}

	return confl;
}

void CardPWAgg::backtrack(const Agg& agg) {
	reportf("BACKTRACKED HEAD\n");

	if (checkingNFex()) {
		setf.push_back(nfex[0]);
		nfex.clear();
	}

	if (checkingNTex()) {
		sett.push_back(ntex[0]);
		ntex.clear();
	}

	if(checkingNF()){
		for(int i=0; i<nf.size(); i++){
			addWatch(nf[i].getLit(), NF, i);
		}
	}

	if(checkingNT()){
		for(int i=0; i<nt.size(); i++){
			addWatch(nt[i].getLit(), NT, i);
		}
	}

	headvalue = l_Undef;
}

void CardPWAgg::getExplanation(vec<Lit>& lits, const AggReason& ar) const {
	for (vsize i = 0; i < as().getWL().size(); i++) {
		const WL& wl = as().getWL()[i];
		if (var(wl.getLit()) != var(ar.getLit()) && value(wl.getLit())
				!= l_Undef) {
			if (as().getSolver()->getPCSolver()->getLevel(var(wl.getLit()))
					!= as().getSolver()->getPCSolver()->getLevel(var(
							ar.getLit()))) {
				lits.push(~wl.getLit());
			} else {
				vl trail =
						as().getSolver()->getPCSolver()->getRecentAssignments();

				bool before = false;
				for (int i = 0; i < trail.size(); i++) {
					if (var(trail[i]) == var(ar.getLit())) {
						break;
					}
					if (var(trail[i]) == var(wl.getLit())) {
						before = true;
						break;
					}
				}
				if (before) {
					lits.push(~wl.getLit());
				}
			}
		}
	}
}
