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

vptw& CardPWAgg::getSet(watchset w) {
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

vptw& CardPWAgg::getWatches(watchset w) {
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

/*
 * Removes a literal from its set and adds it to a watched set
 */
void CardPWAgg::addToWatchedSet(watchset w, int setindex) {
	vptw& set = getSet(w);
	vptw& watches = getWatches(w);
	ptw watch = set[setindex];
	watch->watch()->setIndex(watches.size());
	watches.push_back(watch);
	set[setindex] = set[set.size()-1];
	set.pop_back();
}

void CardPWAgg::addWatchesToSolver(watchset w){
	for(int i=0; i<getWatches(w).size(); i++){
		addWatchToSolver(w, getWatches(w), i);
	}
}

void CardPWAgg::addWatchToSolver(watchset w, const vptw& set, int index) {
	set[index]->watch()->setInUse(true);
	set[index]->watch()->setWatchset(w);
	as().getSolver()->addTempWatch(set[index]->lit(), set[index]->watch());
}

void CardPWAgg::removeWatches(watchset w){
	vptw& watches = getWatches(w);
	vptw& set = getSet(w);

	for(int i=0; i<watches.size(); i++){
		/* TODO ik denk dat iets als dit noodzakelijk is, anders kan backtracken ineens een kleinere watched set krijgen, want hij vindt geen vervanging
		if(value(watches[i].getLit())!=l_Undef){
			remainingwatches.push_back(watches[i]);
			continue;
		}*/

		watches[i]->watch()->setInUse(false);
		watches[i]->watch()->setWatchset(INSET);
		set.push_back(watches[i]);
	}
	watches.clear();
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


	//Create sets and watches
	for(int i=0; i<as().getWL().size(); i++){
		const WL& wl = as().getWL()[i];
		const WL& negwl = WL(~wl.getLit(), wl.getWeight());
		setf.push_back(new ToWatch(asp(), agg.isLower()?negwl:wl));
		sett.push_back(new ToWatch(asp(), agg.isLower()?wl:negwl));
	}

	bool nffailed = false, ntfailed;
	if (agg.isLower()) {
		//Card(S)<=B
		if (checking(NF)) {
			nffailed = !initializeNFL();
		}

		//~Card(S)<=B
		if (checking(NT)) {
			ntfailed = !initializeNTL();
		}
	} else {
		//Card(S)>=B
		if (checking(NF)) {
			nffailed = !initializeNF();
		}

		//~Card(S)>=B
		if (checking(NT)) {
			ntfailed = !initializeNT();
		}
	}

	rClause confl = nullPtrClause;
	if (nffailed) {
		confl = as().getSolver()->notifySolver(~agg.getHead(), new AggReason(agg, ~agg.getHead(), BASEDONCC, false));
		if (confl != nullPtrClause) {
			unsat = true;
		}else{
			sat = true;
		}
		return;
	}
	if (ntfailed) {
		confl = as().getSolver()->notifySolver(agg.getHead(), new AggReason(agg, agg.getHead(), BASEDONCC, false));
		if (confl != nullPtrClause) {
			unsat = true;
			return;
		}else{
			sat = true;
		}
		return;
	}

	//IMPORTANT: only add watches AFTER initialization, otherwise delete is not complete! TODO check if this is always enough
	addWatchesToSolver(NF);
	addWatchesToSolver(NT);

	PWAgg::initialize(unsat, sat);
}

bool CardPWAgg::initializeNF() {
	const Agg& agg = *as().getAgg()[0];
	vptw& set = getSet(NF);
	for (vsize i = 0; i < set.size(); i++) {
		const WL& wl = set[i]->wl();
		if (Weight(nf.size()) < agg.getBound() && value(wl.getLit()) != l_False) {
			addToWatchedSet(NF, i);
			i--;
		}
	}
	return Weight(nf.size()) >= agg.getBound();
}

bool CardPWAgg::initializeNT() {
	const Agg& agg = *as().getAgg()[0];
	vptw& set = getSet(NT);
	for (vsize i = 0; i < set.size(); i++) {
		const WL& wl = set[i]->wl();
		if (Weight(nt.size()) <= Weight(as().getWL().size()) - agg.getBound() && value(wl.getLit()) != l_False) {
			addToWatchedSet(NT, i);
			i--;
		}
	}
	return Weight(nt.size()) > Weight(as().getWL().size()) - agg.getBound();
}

bool CardPWAgg::initializeNTL() {
	const Agg& agg = *as().getAgg()[0];
	vptw& set = getSet(NT);
	for (vsize i = 0; i < set.size(); i++) {
		const WL& wl = set[i]->wl();
		if (Weight(nt.size()) <= agg.getBound() && value(wl.getLit()) != l_False) {
			addToWatchedSet(NT, i);
			i--;
		}
	}
	return Weight(nt.size()) > agg.getBound();
}

bool CardPWAgg::initializeNFL() {
	const Agg& agg = *as().getAgg()[0];
	vptw& set = getSet(NF);
	for (vsize i = 0; i < set.size(); i++) {
		const WL& wl = set[i]->wl();
		if (Weight(nf.size()) < Weight(as().getWL().size()) - agg.getBound() && value(wl.getLit()) != l_False) {
			addToWatchedSet(NF, i);
			i--;
		}
	}
	return Weight(nf.size()) >= Weight(as().getWL().size()) - agg.getBound();
}

bool CardPWAgg::initializeEX(watchset w) {
	bool found = false;
	vptw& set = getSet(w);
	for (vsize i = 0; !found && i < set.size(); i++) {
		if (value(set[i]->wl().getLit()) != l_False) {
			addToWatchedSet(w, i);
			i--;
			found = true;
		}
	}
	return found;
}

bool CardPWAgg::replace(vsize index, watchset w) {
	bool found = false;
	vptw& set = getSet(w);
	vptw& watches = getWatches(w);

	for (vsize i = 0; !found && i < set.size(); i++) {
		ptw tw = set[i];
		if (value(tw->lit()) != l_False) {
			set[i] = watches[index];
			watches[index] = tw;
			addWatchToSolver(w, watches, index);
			found = true;
		}
	}
	return found;
}

rClause CardPWAgg::propagate(const Lit& p, const Watch& watch) {
	rClause confl = nullPtrClause;

	PWatch const * pw = dynamic_cast<PWatch const *> (&watch);
	const PWatch& w = *pw;

	if(!w.isInUse()){
		w.setWatchset(INSET);
		return confl;
	}

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

	if (!found) {
		if (checking(NFEX)) {
			// propagate all others in NF and propagate NFex
			for (vsize i = 0; confl == nullPtrClause && i < nf.size(); i++) {
				if (i == w.getIndex() && !isEX(w.getWatchset())) {
					continue;
				}
				confl = as().getSolver()->notifySolver(nf[i]->lit(), new AggReason(*as().getAgg()[0], nf[i]->lit(), BASEDONCC, false));
			}
			if (confl == nullPtrClause) {
				for (vsize i = 0; confl == nullPtrClause && i < nfex.size(); i++) {
					if (i == w.getIndex() && isEX(w.getWatchset())) {
						continue;
					}
					confl = as().getSolver()->notifySolver(nfex[i]->lit(), new AggReason(*as().getAgg()[0], nfex[i]->lit(), BASEDONCC, false));
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
				confl = as().getSolver()->notifySolver(nt[i]->lit(), new AggReason(*as().getAgg()[0], nt[i]->lit(), BASEDONCC, false));
			}
			if (confl == nullPtrClause) {
				for (vsize i = 0; confl == nullPtrClause && i < ntex.size(); i++) {
					if (i == w.getIndex() && isEX(w.getWatchset())) {
						continue;
					}
					confl = as().getSolver()->notifySolver(ntex[i]->lit(), new AggReason(*as().getAgg()[0], ntex[i]->lit(), BASEDONCC, false));
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
	}

	if(!found){
		//If in the end not replacement was found, we add the previous one again to the solver
		addWatchToSolver(w.getWatchset(), getWatches(w.getWatchset()), w.getIndex());
	}else{
		//otherwise, it is marked as no longer in use
		w.setWatchset(INSET);
		w.setInUse(false);
	}

	return confl;
}

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
				confl = as().getSolver()->notifySolver(nf[i]->lit(), new AggReason(*as().getAgg()[0], nf[i]->lit(), BASEDONCC, false));
			}
		}else{
			addWatchesToSolver(NFEX);
		}
	}

	if (checking(NTEX)) {
		if (!initializeEX(NTEX)) {
			for (vsize i = 0; confl == nullPtrClause && i < nt.size(); i++) {
				confl = as().getSolver()->notifySolver(nt[i]->lit(), new AggReason(*as().getAgg()[0], nt[i]->lit(), BASEDONCC, false));
			}
		}else{
			addWatchesToSolver(NTEX);
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
		addWatchesToSolver(NF);
	}

	if(checking(NT)){
		if(agg.isLower()){
			initializeNTL();
		}else{
			initializeNT();
		}
		addWatchesToSolver(NT);
	}
}

/*
 * @pre: p has been assigned in the current decision level!
 */
bool CardPWAgg::assertedBefore(const Var& l, const Var& p) const {
	PCSolver* pcsol = as().getSolver()->getPCSolver();

	//Check if level is lower
	if(pcsol->getLevel(l) < pcsol->getLevel(p)){
		return true;
	}

	const vl& trail = pcsol->getRecentAssignments();
	bool before = true;
	for (int i = 0; i < trail.size(); i++) {
		if (var(trail[i]) == l) { // l encountered first, so before
			break;
		}
		if (var(trail[i]) == p) { // p encountered first, so after
			before = false;
			break;
		}
	}

	return before;
}

void CardPWAgg::getExplanation(vec<Lit>& lits, const AggReason& ar) const {
	const Lit& head = ar.getAgg().getHead();
	if(value(head)!=l_Undef && var(ar.getLit())!=var(head)){
		if(assertedBefore(var(head), var(ar.getLit()))){
			lits.push(value(head)==l_True?~head:head);
		}
	}

	for (vsize i = 0; i < as().getWL().size(); i++) {
		const WL& wl = as().getWL()[i];
		if (var(wl.getLit()) != var(ar.getLit()) && value(wl.getLit()) != l_Undef) {
			if(assertedBefore(var(wl.getLit()), var(ar.getLit()))){
				lits.push(value(wl.getLit())==l_True?~wl.getLit():wl.getLit());
			}
		}
	}
}
