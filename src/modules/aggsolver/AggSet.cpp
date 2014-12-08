/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mari��n, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#include "modules/aggsolver/AggSet.hpp"
#include "modules/aggsolver/AggProp.hpp"
#include "modules/aggsolver/AggPrint.hpp"
#include "external/utils/ContainerUtils.hpp"
#include "external/ConstraintVisitor.hpp"
#include "utils/Print.hpp"
#include <cmath>

#include "satsolver/heuristics/Heuristics.hpp"

using namespace std;
using namespace MinisatID;

TypedSet::TypedSet(PCSolver* solver, int setid, AggProp const * const w, const vwl& wls, bool usewatches,
		const std::vector<TempAgg*>& aggr, bool optim) :
		Propagator(solver, "aggregate"),
		type(w),
		prop(NULL),
		setid(setid),
		usingwatches(usewatches){
	setWL(wls);
	MAssert(not optim || aggr.size()==1);

	if (verbosity() >= 2) {
		clog << "Added ";
		MinisatID::print(10000, *this, true);
	}

	for (auto agg : aggr) {
		addAgg(*agg, optim);
	}

	prop = getType().createPropagator(this);
	bool sat = false;
	bool unsat = false;
	getProp()->initialize(unsat, sat); // IMPORTANT: might throw, in which case the destructor is NOT called and prop and the aggregates will not be deleted
	if (not sat) {
		MAssert(unsat || getAgg().size()>0);
	} else {
		notifyNotPresent();
	}

#ifdef DEBUG
	//Check each aggregate knows it index in the set
	for (auto i = getAgg().cbegin(); i<getAgg().cend(); ++i) {
		MAssert(this==(*i)->getSet());
		MAssert(getAgg()[(*i)->getIndex()]==(*i));
	}
#endif

	if (unsat) {
		if (verbosity() >= 3) {
			clog << "Initializing aggregate set, unsat detected.\n";
		}
		getPCSolver().notifyUnsat();
	}

	// NOTE: important: only pass the object around when the object will be created (had an issue where an exception was thrown INSIDE the constructor AFTER passing the object to another class)
	getPCSolver().accept(this);
	getPCSolver().accept(this, EV_MODELFOUND);
	getPCSolver().accept(this, EV_BACKTRACK);
}

TypedSet::~TypedSet() {
	deleteList<Agg>(aggregates);
	delete (prop);
	for(auto atom2reason:reasons){
		if(atom2reason.second!=NULL){
			delete(atom2reason.second);
		}
	}
}

void TypedSet::addAgg(const TempAgg& tempagg, bool optim) {
	auto agg = new Agg(this, tempagg, optim);
	aggregates.push_back(agg);
	agg->setIndex(aggregates.size() - 1);
	if (getPCSolver().verbosity() >= 2) {
		MinisatID::print(getPCSolver().verbosity(), *agg);
		clog << "\n";
	}
}

void TypedSet::acceptForBacktrack() {
	auto level = getPCSolver().getCurrentDecisionLevel();
	if(backtrack.size()==0 || backtrack.back()<level){
		backtrack.push_back(level);
	}
}

// NOTE: could prevent calling backtrack each time and instead pass more knowledge to the eventqueue
void TypedSet::notifyBacktrack(int untillevel, const Lit& decision) {
	MAssert(getProp()!=NULL);

	if(backtrack.size()>0 && backtrack.back()>untillevel){
		int lower = 0;
		for(auto i=backtrack.cbegin(); i<backtrack.cend(); ++i){
			if(*i<=untillevel){
				lower++;
			}else{
				break;
			}
		}
		backtrack.resize(lower);
		getProp()->backtrack(untillevel);
	}
	Propagator::notifyBacktrack(untillevel, decision);
}

void TypedSet::removeAggs(const std::set<Agg*>& del) {
	for (auto agg = getAggNonConst().begin(); agg < getAggNonConst().end();) {
		if (del.find(*agg) != del.cend()) {
			agg = getAggNonConst().erase(agg);
		} else {
			++agg;
		}
	}
	int index = 0;
	for (auto agg = getAgg().cbegin(); agg != getAgg().cend(); ++agg, index++) {
		(*agg)->setIndex(index);
	}
}

rClause TypedSet::notifySolver(AggReason* ar) {
	auto p = ar->getPropLit();

	if (modes().bumpaggonnotify) {
		//Decreases sokoban and dansmee performance, increases fastfood
		getPCSolver().getHeuristic().notifyTypedSet(var(p));
	}

	//If a propagation will be done or conflict (not already true), then add the learned clause first
	if (value(p) != l_True && getPCSolver().modes().aggclausesaving < 2) {
		ar->getAgg().getSet()->addExplanation(*ar);
	}

	if (value(p) == l_False) {
		if (verbosity() >= 3) {
			clog << "Deriving conflict in ";
			clog << toString(p, l_True);
			clog << " because of the aggregate expression ";
			MinisatID::print(verbosity(), ar->getAgg(), true);
		}
		MAssert(getPCSolver().modes().aggclausesaving>1 || ar->hasClause());

		MAssert(reasons[var(p)]==NULL || getPCSolver().modes().aggclausesaving>1 || reasons[var(p)]->hasClause());
		AggReason* old_ar = reasons[var(p)];
		reasons[var(p)] = ar;
		rClause confl = getExplanation(p); //Reason manipulation because getexplanation uses that reason!
		reasons[var(p)] = old_ar;
		delete ar; // Have to delete before addLearnedClause, as internally it might lead to backtrack and removing the reason
		getPCSolver().addConflictClause(confl);
		return confl;
	} else if (value(p) == l_Undef) {
		if (verbosity() >= 3) {
			clog << "Deriving ";
			clog << toString(p, l_True);
			clog << " because of the aggregate expression ";
			MinisatID::print(verbosity(), ar->getAgg(), true);
		}

		//Keeping a reason longer than necessary is not a problem => if after backtracking still unknown, then no getexplanation, if it becomes known,
		//either this is overwritten or the propagation stems from another module, which will be asked for the explanation
		if (reasons[var(p)] != NULL) {
			delete reasons[var(p)];
		}
		reasons[var(p)] = ar;

		if (getPCSolver().modes().aggclausesaving < 1) {
			auto c = getPCSolver().createClause(ar->getClause(), true);
			getPCSolver().addLearnedClause(c);
		}else {
			getPCSolver().setTrue(p, this);
		}
	} else {
		delete ar;
	}
	return nullPtrClause;
}

void TypedSet::addExplanation(AggReason& ar) const {
	Disjunction lits({ar.getPropLit()});
	getProp()->getExplanation(lits.literals, ar);
	ar.setClause(lits);

	if (verbosity() >= 3) {
		std::clog << "Explanation for deriving " << toString(ar.getPropLit());
		std::clog << " in expression ";
		print(verbosity(), ar.getAgg(), false);
		std::clog << " is ";
		for (uint i = 0; i < lits.literals.size(); ++i) {
			std::clog << " " << toString(lits.literals[i]);
		}
		std::clog << "\n";
	}
}

void TypedSet::notifypropagate(Watch* w) {
	getProp()->propagate(w);
	getPCSolver().acceptForPropagation(this, PRIORITY::FAST);
}

rClause TypedSet::notifypropagate() {
	return getProp()->propagateAtEndOfQueue();
}

rClause TypedSet::notifyFullAssignmentFound() {
#ifdef DEBUG // Check consistency of aggregates
	bool twovalued = true;
	for(auto i=getWL().cbegin(); twovalued && i<getWL().cend(); ++i) {
		if(value((*i).getLit())==l_Undef) {
			twovalued = false;
		}
	}
	if(twovalued) {
		auto w = getType().getValue(*this);
		for(auto j=getAgg().cbegin(); j<getAgg().cend(); ++j) {
			if(verbosity()>=3) {
				MinisatID::print(10, **j, true);
			}
			auto headval = value((*j)->getHead());
			if((*j)->getSem()==AggSem::OR) {
				MAssert(headval==l_True || isSatisfied(**j, w, w));
			} else {
				MAssert((headval==l_False && isFalsified(**j, w, w)) || (headval==l_True && isSatisfied(**j, w, w)));
			}
		}
	}
#endif
	return nullPtrClause;
}

void TypedSet::accept(ConstraintVisitor& visitor){
	auto set = WLSet(getSetID(), getWL());
	visitor.add(set);
	for(auto agg:getAgg()){
		visitor.add(Aggregate(agg->getHead(), getSetID(), agg->getBound(), agg->getType(), agg->getSign(), agg->getSem(), -1, false));
	}
}

//Returns OWNING pointer. This has proven to be faster than always adding generated explanations to the clause store!
rClause TypedSet::getExplanation(const Lit& p) {
	MAssert(reasons[var(p)] != NULL);
	AggReason& ar = *reasons[var(p)];

	rClause c = nullPtrClause;
	if (getPCSolver().modes().aggclausesaving < 2) {
		MAssert(ar.hasClause());
	} else {
		ar.getAgg().getSet()->addExplanation(ar);
	}

	c = getPCSolver().createClause(ar.getClause(), true);

	//do not add each clause to SAT-solver: real slowdown for e.g. magicseries

	return c;
}

void MinisatID::makeSumSetPositive(TypedSet& set){

#ifdef NOARBITPREC
	//Test whether the total sum of the weights is not infinity for intweights
	Weight total(0);
	for (auto i = set.getWL().cbegin(); i < set.getWL().cend(); ++i) {
		if (INT_MAX - total < i->getWeight()) {
			throw idpexception("The total sum of weights exceeds max-int, correctness cannot be guaranteed in limited precision.\n");
		}
		total += abs(i->getWeight());
	}
#endif

	//Calculate the total negative weight to make all weights positive
	vwl wlits2;
	Weight totalneg(0);
	for (auto i = set.getWL().cbegin(); i < set.getWL().cend(); ++i) {
		if (i->getWeight() < 0) {
			totalneg -= i->getWeight();
		}
	}
	if (totalneg > 0) {
		//Important: negate literals of with negative weights!
		for (auto i = set.getWL().cbegin(); i < set.getWL().cend(); ++i) {
			if (i->getWeight() < 0) {
				wlits2.push_back(WL(~i->getLit(), abs(i->getWeight())));
			} else {
				wlits2.push_back(*i);
			}
		}
		set.setWL(wlits2);
		for (auto i = set.getAgg().cbegin(); i < set.getAgg().cend(); ++i) {
			Weight b = set.getType().add((*i)->getBound(), totalneg);
			(*i)->setBound(AggBound((*i)->getSign(), b));
		}
	}
}
