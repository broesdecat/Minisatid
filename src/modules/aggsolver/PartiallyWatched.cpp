#include "modules/aggsolver/PartiallyWatched.hpp"
#include "modules/aggsolver/FullyWatched.hpp"
#include "modules/aggsolver/AggPrint.hpp"
#include "modules/AggSolver.hpp"
#include "theorysolvers/PCSolver.hpp"

#include <stdint.h>
#include <inttypes.h>
#include <limits.h>

using namespace std;
using namespace MinisatID;
using namespace Aggrs;

void Aggrs::printWatches(AggSolver* const solver, const vvpw& tempwatches){
	for(vsize i=0; i<2*solver->nVars(); i++){
		bool found = false;
		for(vsize j=0; !found && j<tempwatches[i].size(); j++){
			for(vsize k=0; !found && k<tempwatches[i][j]->getSet()->getAgg().size(); k++){
				PWatch* watch = dynamic_cast<PWatch*>(tempwatches[i][j]);
				if(watch!=NULL && watch->isInUse()){
					found = true;
				}
				GenPWatch* watch2 = dynamic_cast<GenPWatch*>(tempwatches[i][j]);
				if(watch2!=NULL && watch2->getWatchset()!=INSET){
					found = true;
				}
			}
		}

		if(!found){
			continue;
		}

		report("    Watch "); gprintLit(toLit(i)); report(" used by: \n");
		for(vsize j=0; j<tempwatches[i].size(); j++){
			for(vsize k=0; k<tempwatches[i][j]->getSet()->getAgg().size(); k++){
				PWatch* watch = dynamic_cast<PWatch*>(tempwatches[i][j]);
				if(watch!=NULL && watch->isInUse()){
					report("        ");
					print(*tempwatches[i][j]->getSet()->getAgg()[k], true);
				}
				GenPWatch* watch2 = dynamic_cast<GenPWatch*>(tempwatches[i][j]);
				if(watch2!=NULL && watch2->getWatchset()!=INSET){
					report("        ");
					print(*tempwatches[i][j]->getSet()->getAgg()[k], true);
				}
			}
		}
	}
	report("\n");
}

///////
//PW as().getAgg
///////

inline vptw& CardPWAgg::getSet(WATCHSET w) {
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

inline vptw& CardPWAgg::getWatches(WATCHSET w) {
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

inline bool CardPWAgg::checking(WATCHSET w) const{
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
 * Removes a literal from its set and adds it to a watched set
 */
void CardPWAgg::addToWatchedSet(WATCHSET w, vsize setindex) {
	vptw& set = getSet(w);
	vptw& watches = getWatches(w);
	ptw watch = set[setindex];
	watches.push_back(watch);
	set[setindex] = set[set.size()-1];
	set.pop_back();
	watch->setWatchset(w);
	watch->setIndex(watches.size()-1);
}

void CardPWAgg::addWatchesToSolver(WATCHSET w){
	for(vsize i=0; i<getWatches(w).size(); i++){
		addWatchToSolver(w, getWatches(w), i);
	}
}

void CardPWAgg::addWatchToSolver(WATCHSET w, const vptw& set, vsize index) {
	assert(set[index]->getIndex()==index);
	set[index]->setInUse(true);
	getSolver()->addTempWatch(~set[index]->getLit(), set[index]);
}

void CardPWAgg::removeWatches(WATCHSET w){
	vptw& watches = getWatches(w);
	vptw& set = getSet(w);

	for(vsize i=0; i<watches.size(); i++){
		/* TODO ik denk dat iets als dit noodzakelijk is, anders kan backtracken ineens een kleinere watched set krijgen, want hij vindt geen vervanging
		if(value(watches[i].getLit())!=l_Undef){
			remainingwatches.push_back(watches[i]);
			continue;
		}*/

		watches[i]->setInUse(false);
		watches[i]->setWatchset(INSET);
		watches[i]->setIndex(-1);
		set.push_back(watches[i]);
	}
	watches.clear();
}

PWAgg::PWAgg(TypedSet* set) :
	Propagator(set) {
}

CardPWAgg::CardPWAgg(TypedSet* set) :
	PWAgg(set), headvalue(l_Undef), headproplevel(-1), headpropagatedhere(false) {
	startsetf.push_back(0);
	startsett.push_back(0);
}

CardPWAgg::~CardPWAgg(){
	deleteList<tw>(nf);
	deleteList<tw>(nt);
	deleteList<tw>(nfex);
	deleteList<tw>(ntex);
	deleteList<tw>(setf);
	deleteList<tw>(sett);
}

void CardPWAgg::initialize(bool& unsat, bool& sat) {
	// All that we can't handle at the moment is transformed into a fixed watch sum aggregate.
	assert(getSetp()->getAgg().size()==1);

	const Agg& agg = *getSetp()->getAgg()[0];

	//Create sets and watches
	for(vsize i=0; i<getSetp()->getWL().size(); i++){
		const WL& wl = getSetp()->getWL()[i];
		const WL& negwl = WL(~wl.getLit(), wl.getWeight());
		setf.push_back(new PWatch(getSetp(), agg.hasUB()?negwl:wl, i, INSET));
		sett.push_back(new PWatch(getSetp(), agg.hasUB()?wl:negwl, i, INSET));
	}

	bool nffailed = false, ntfailed = false;
	if (agg.hasUB()) {
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
		confl = getSolver()->notifySolver(new AggReason(agg, BASEDONCC, ~agg.getHead(), false));
		if (confl != nullPtrClause) {
			unsat = true;
		}else{
			sat = true;
		}
		return;
	}
	if (ntfailed) {
		confl = getSolver()->notifySolver(new AggReason(agg, BASEDONCP, agg.getHead(), false));
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
	const Agg& agg = *getSetp()->getAgg()[0];
	vptw& set = getSet(NF);
	for (int i = 0; i < (int)set.size(); i++) {
		const WL& wl = set[i]->getWL();
		if (Weight(nf.size()) < agg.getCertainBound() && propagatedValue(wl.getLit()) != l_False) {
			addToWatchedSet(NF, i);
			i--;
		}
	}
	return Weight(nf.size()) >= agg.getCertainBound();
}

bool CardPWAgg::initializeNT() {
	const Agg& agg = *getSetp()->getAgg()[0];
	vptw& set = getSet(NT);
	for (int i = 0; i < (int)set.size(); i++) {
		const WL& wl = set[i]->getWL();
		if (Weight(nt.size()) <= Weight(getSetp()->getWL().size()) - agg.getCertainBound() && propagatedValue(wl.getLit()) != l_False) {
			addToWatchedSet(NT, i);
			i--;
		}
	}
	return Weight(nt.size()) > Weight(getSetp()->getWL().size()) - agg.getCertainBound();
}

bool CardPWAgg::initializeNTL() {
	const Agg& agg = *getSetp()->getAgg()[0];
	vptw& set = getSet(NT);
	for (int i = 0; i < (int)set.size(); i++) {
		const WL& wl = set[i]->getWL();
		if (Weight(nt.size()) <= agg.getCertainBound() && propagatedValue(wl.getLit()) != l_False) {
			addToWatchedSet(NT, i);
			i--;
		}
	}
	return Weight(nt.size()) > agg.getCertainBound();
}

bool CardPWAgg::initializeNFL() {
	const Agg& agg = *getSetp()->getAgg()[0];
	vptw& set = getSet(NF);
	for (int i = 0; i < (int)set.size(); i++) {
		const WL& wl = set[i]->getWL();
		if (Weight(nf.size()) < Weight(getSetp()->getWL().size()) - agg.getCertainBound() && propagatedValue(wl.getLit()) != l_False) {
			addToWatchedSet(NF, i);
			i--;
		}
	}
	return Weight(nf.size()) >= Weight(getSetp()->getWL().size()) - agg.getCertainBound();
}

bool CardPWAgg::initializeEX(WATCHSET w) {
	bool found = false;
	vptw& set = getSet(w);
	for (int i = 0; !found && i < (int)set.size(); i++) {
		if (propagatedValue(set[i]->getLit()) != l_False) {
			addToWatchedSet(w, i);
			i--;
			found = true;
		}
	}
	return found;
}

bool CardPWAgg::replace(vsize index, WATCHSET w) {
	bool found = false;
	vptw& set = getSet(w);
	vptw& watches = getWatches(w);

	for (vsize i = 0/*ss*/; !found && i < set.size(); i++) {
		ptw tw = set[i];
		if (propagatedValue(tw->getLit()) != l_False) {
			watches[index]->setIndex(-1);
			watches[index]->setWatchset(INSET);
			watches[index]->setInUse(false);
			set[i] = watches[index];
			watches[index] = tw;
			tw->setWatchset(w);
			tw->setIndex(index);
			addWatchToSolver(w, watches, index);
			found = true;
		}
	}
	return found;
}

rClause CardPWAgg::propagate(const Lit& p, Watch* watch, int level) {
	rClause confl = nullPtrClause;

	PWatch* pw = dynamic_cast<PWatch *>(watch);
	PWatch& w = *pw;

#ifdef DEBUG
	/*
	 * If w inset: check if really in set (iterate), if so, set inuse false and return
	 * If w in watch: check if really at the given index in the set and inuse has to be true
	 */
	if(w.getWatchset()==INSET){
		assert(w.getIndex()==-1);
		bool found = false;
		for(vsize i=0; !found && i<getSet(NF).size(); i++){
			if(getSet(NF)[i]==pw){
				found = true;
			}
		}
		for(vsize i=0; !found && i<getSet(NT).size(); i++){
			if(getSet(NT)[i]==pw){
				found = true;
			}
		}
		assert(found);
	}else{
		assert(getWatches(w.getWatchset())[w.getIndex()]==pw);
	}
#endif

	if(w.getWatchset()==INSET){
		w.setInUse(false);
		assert(w.getIndex()==-1);
		return confl;
	}

	assert(w.getIndex()!=-1);

	if(!w.isInUse()){
		w.setWatchset(INSET);
		w.setIndex(-1);
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
			//TODO if i would here add also an assertion that i>=0, then it would be completely safe comparisons (except for the size)
			for (int i = 0; confl == nullPtrClause && ((uint)i) < nf.size(); i++) {
				if (i == w.getIndex() && !isEX(w.getWatchset())) {
					continue;
				}
				confl = getSolver()->notifySolver(new AggReason(*getSetp()->getAgg()[0], BASEDONCC, nf[i]->getLit(), false));
			}
			if (confl == nullPtrClause) {
				for (int i = 0; confl == nullPtrClause && ((uint)i) < nfex.size(); i++) {
					if (i == w.getIndex() && isEX(w.getWatchset())) {
						continue;
					}
					confl = getSolver()->notifySolver(new AggReason(*getSetp()->getAgg()[0], BASEDONCC, nfex[i]->getLit(), false));
				}
			}
		} else if (isF(w.getWatchset()) && checking(NF)) {
			//propagate head false
			Lit l = ~getSetp()->getAgg()[0]->getHead();
			confl = getSolver()->notifySolver(new AggReason( *getSetp()->getAgg()[0], BASEDONCC, l, false));
			if(confl==nullPtrClause){
				headpropagatedhere = true;
			}
		} else if (checking(NTEX)) {
			// propagate all others in NF and propagate NFex
			for (int i = 0; confl == nullPtrClause && ((uint)i) < nt.size(); i++) {
				if (i == w.getIndex() && !isEX(w.getWatchset())) {
					continue;
				}
				confl = getSolver()->notifySolver(new AggReason(*getSetp()->getAgg()[0], BASEDONCP, nt[i]->getLit(), false));
			}
			if (confl == nullPtrClause) {
				for (int i = 0; confl == nullPtrClause && ((uint)i) < ntex.size(); i++) {
					if (i == w.getIndex() && isEX(w.getWatchset())) {
						continue;
					}
					confl = getSolver()->notifySolver(new AggReason(*getSetp()->getAgg()[0], BASEDONCP, ntex[i]->getLit(), false));
				}
			}
		} else if (!isF(w.getWatchset()) && checking(NT)) {
			//propagate head true
			Lit l = getSetp()->getAgg()[0]->getHead();
			confl = getSolver()->notifySolver(new AggReason( *getSetp()->getAgg()[0], BASEDONCP, l, false));
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
		w.setInUse(false);
	}

	if(w.getWatchset()!=INSET){
		assert(getWatches(w.getWatchset())[w.getIndex()]==pw);
	}

	return confl;
}

/**
 * When scrapping the stack, a problem arose that a literal might throw a conflict where in fact a later one was the real cause for the conflict,
 * leading to an incomplete reason clause. So here we check which of the conflicting ones was asserted last and throw that conflict.
 * But the problem then remains, that not all of those potential propagations and conflicts ever become watches (because the latest truth value is used)
 * and this can only be helped by using the current truth value, which is what we will do.
 */
rClause CardPWAgg::propagate(int level, const Agg& agg, bool headtrue) {
	if(headpropagatedhere){
		//TODO deze check zou niet noodzakelijk mogen zijn voor de correctheid, maar is dat nu wel. Probleem is
		//dat hij soms bij head propageren geen extension vindt en dan alles propageert, maar eigenlijk
		//hoeft dat niet als een volledig true conflict set gevonden kan worden
		return nullPtrClause;
	}

	assert(headvalue==l_Undef);
	assert(nfex.size() == 0 && ntex.size() == 0);

	headvalue = value(agg.getHead());
	headproplevel = level;

	getSolver()->addToBackTrail(getSetp());

	rClause confl = nullPtrClause;

	if(!checking(NF)){
		removeWatches(NF);
	}

	if(!checking(NT)){
		removeWatches(NT);
	}

	if (checking(NFEX)) {
		if (!initializeEX(NFEX)) {
			for (vsize i = 0; confl == nullPtrClause && i < nf.size(); i++) {
				confl = getSolver()->notifySolver(new AggReason(*getSetp()->getAgg()[0], BASEDONCC, nf[i]->getLit(), false));
			}
		}else{
			addWatchesToSolver(NFEX);
		}
	}

	if (checking(NTEX)) {
		if (!initializeEX(NTEX)) {
			for (vsize i = 0; confl == nullPtrClause && i < nt.size(); i++) {
				confl = getSolver()->notifySolver(new AggReason(*getSetp()->getAgg()[0], BASEDONCP, nt[i]->getLit(), false));
			}
		}else{
			addWatchesToSolver(NTEX);
		}
	}

	return confl;
}

void CardPWAgg::backtrack(int nblevels, int untillevel) {
	if(headproplevel>untillevel){
		headpropagatedhere = false;
		headproplevel = -1;

		if (checking(NFEX)) {
			removeWatches(NFEX);
		}

		if (checking(NTEX)) {
			removeWatches(NTEX);
		}

		headvalue = l_Undef;

		Agg& agg = *getSetp()->getAgg()[0];
		if(checking(NF)){
			if(agg.hasUB()){
				initializeNFL();
			}else{
				initializeNF();
			}
			addWatchesToSolver(NF);
		}

		if(checking(NT)){
			if(agg.hasUB()){
				initializeNTL();
			}else{
				initializeNT();
			}
			addWatchesToSolver(NT);
		}
	}
}

void CardPWAgg::getExplanation(vec<Lit>& lits, const AggReason& ar) {
	//FIXME INCORRECT!
	const PCSolver& pcsol = *getSolver()->getPCSolver();
	const Lit& head = ar.getAgg().getHead();
	if(value(head)!=l_Undef && var(ar.getPropLit())!=var(head)){
		if(pcsol.assertedBefore(var(head), var(ar.getPropLit()))){
			lits.push(value(head)==l_True?~head:head);
		}
	}

	Lit comparelit = ar.getPropLit();

	for (vsize i = 0; i < getSetp()->getWL().size(); i++) {
		const WL& wl = getSetp()->getWL()[i];
/*		if(ar.getExpl()==BASEDONCC){ //Monotone one (one in the set) propagated: take only false monotone ones
			if(value(wl.getLit())==(ar.getAgg().hasLB()?l_True:l_False)){
				continue;
			}
		}
		if(ar.getExpl()==BASEDONCP){ //Anti-monotone one (one not in the set) propagated: take only true monotone ones
			if(value(wl.getLit())==(ar.getAgg().hasLB()?l_False:l_True)){
				continue;
			}
		}*/
		if (var(wl.getLit()) != var(comparelit) && value(wl.getLit()) != l_Undef) {
			if(pcsol.assertedBefore(var(wl.getLit()), var(comparelit))){
				lits.push(value(wl.getLit())==l_True?~wl.getLit():wl.getLit());
			}
		}
	}
}
