/*
 * AggProp.cpp
 *
 *  Created on: Oct 26, 2010
 *      Author: broes
 */

#include <limits>
#include "solvers/modules/aggsolver/AggProp.hpp"

using namespace std;
using namespace MinisatID;

typedef numeric_limits<int> intlim;

AggProp* AggProp::max = new MaxProp();
AggProp* AggProp::sum = new SumProp();
AggProp* AggProp::card = new CardProp();
AggProp* AggProp::prod = new ProdProp();

bool MaxProp::isMonotone(const Agg& agg, const WL& l) const {
	return (agg.isLower() && l.getWeight() <= agg.getBound()) || (agg.isUpper());
}

bool SumProp::isMonotone(const Agg& agg, const WL& l) const {
	return (agg.isLower() && l.getWeight() < 0) || (agg.isUpper() && l.getWeight() > 0);
}

bool ProdProp::isMonotone(const Agg& agg, const WL& l) const {
	assert(l.getWeight() == 0 || l.getWeight() >= 1);
	return agg.isUpper();
}

Weight SumProp::add(const Weight& lhs, const Weight& rhs) const {
#ifdef INTWEIGHT
	if(lhs>0 && rhs > 0 && intlim::max()-lhs < rhs) {
		return intlim::max();
	} else if(lhs<0 && rhs<0 && intlim::min()-lhs>rhs) {
		return intlim::min();
	}
#endif
	return lhs + rhs;
}

Weight SumProp::remove(const Weight& lhs, const Weight& rhs) const {
	return lhs - rhs;
}

Weight SumProp::getBestPossible(TypedSet* set) const {
	Weight max = set->getESV();
	for (vwl::const_iterator j = set->getWL().begin(); j < set->getWL().end(); j++) {
		max = this->add(max, (*j).getWeight());
	}
	return max;
}

Weight SumProp::getCombinedWeight(const Weight& one, const Weight& two) const {
	return this->add(one, two);
}

WL SumProp::handleOccurenceOfBothSigns(const WL& one, const WL& two, TypedSet* set) {
	if (one.getWeight() < two.getWeight()) {
		set->setESV(set->getESV() + one.getWeight());
		return WL(two.getLit(), this->remove(two.getWeight(), one.getWeight()));
	} else {
		set->setESV(set->getESV() + two.getWeight());
		return WL(one.getLit(), this->remove(one.getWeight(), two.getWeight()));
	}
}

///////
// CARD Prop
///////

Weight CardProp::getBestPossible(TypedSet* set) const {
	Weight max = set->getESV();
	for (vwl::const_iterator j = set->getWL().begin(); j < set->getWL().end(); j++) {
		max = this->add(max, (*j).getWeight());
	}
	return max;
}

Weight CardProp::add(const Weight& lhs, const Weight& rhs) const {
#ifdef INTWEIGHT
	if(lhs>0 && rhs > 0 && intlim::max()-lhs < rhs) {
		return intlim::max();
	} else if(lhs<0 && rhs<0 && intlim::min()-lhs>rhs) {
		return intlim::min();
	}
#endif
	return lhs + rhs;
}

Weight CardProp::remove(const Weight& lhs, const Weight& rhs) const {
	return lhs - rhs;
}

Weight CardProp::getCombinedWeight(const Weight& one, const Weight& two) const {
	return this->add(one, two);
}

WL CardProp::handleOccurenceOfBothSigns(const WL& one, const WL& two, TypedSet* set) {
	if (one.getWeight() < two.getWeight()) {
		set->setESV(set->getESV() + one.getWeight());
		return WL(two.getLit(), this->remove(two.getWeight(), one.getWeight()));
	} else {
		set->setESV(set->getESV() + two.getWeight());
		return WL(one.getLit(), this->remove(one.getWeight(), two.getWeight()));
	}
}

///////
// MAX Prop
///////

Weight MaxProp::getBestPossible(TypedSet* set) const {
	return set->getWL().back().getWeight();
}

Weight MaxProp::getCombinedWeight(const Weight& first, const Weight& second) const {
	return first > second ? first : second;
}

WL MaxProp::handleOccurenceOfBothSigns(const WL& one, const WL& two, TypedSet* set) {
	if (one.getWeight() > two.getWeight()) {
		if (set->getESV() < two.getWeight()) {
			set->setESV(two.getWeight());
		}
		return one;
	} else {
		if (set->getESV() < one.getWeight()) {
			set->setESV(one.getWeight());
		}
		return two;
	}
}

///////
// PROD Prop
///////

Weight ProdProp::getBestPossible(TypedSet* set) const {
	Weight max = set->getESV();
	for (vwl::const_iterator j = set->getWL().begin(); j < set->getWL().end(); j++) {
		max = this->add(max, (*j).getWeight());
	}
	return max;
}

Weight ProdProp::add(const Weight& lhs, const Weight& rhs) const {
#ifdef INTWEIGHT
	bool sign = false;
	Weight l = lhs, r = rhs;
	if(l<0) {
		l= -l;
		sign = true;
	}
	if(r<0) {
		r = -r;
		sign = !sign;
	}
	if(intlim::max()/l < r) {
		return sign?intlim::min():intlim::max();
	}
#endif
	return lhs * rhs;
}

Weight ProdProp::remove(const Weight& lhs, const Weight& rhs) const {
	Weight w = 0;
	if (rhs != 0) {
		w = lhs / rhs;
		if (w == 1 && lhs > rhs) {
			w = 2;
		}
	}

	return w;
}

Weight ProdProp::getCombinedWeight(const Weight& one, const Weight& two) const {
	return this->add(one, two);
}

WL ProdProp::handleOccurenceOfBothSigns(const WL& one, const WL& two, TypedSet* set) {
	//NOTE: om dit toe te laten, ofwel bij elke operatie op en literal al zijn voorkomens overlopen
	//ofwel aggregaten voor doubles ondersteunen (het eerste is eigenlijk de beste oplossing)
	//Mogelijke eenvoudige implementatie: weigts bijhouden als doubles (en al de rest als ints)
	report("Product aggregates in which both the literal and its negation occur "
		"are currently not supported. Replace ");
	gprintLit(one.getLit());
	report("or ");
	gprintLit(two.getLit());
	report("by a tseitin.\n");
	throw idpexception("Atoms in product aggregates have to be unique.\n");
}

///////
// TypedSet
///////

void CalcAgg::initialize(bool& unsat, bool& sat) {
	/*prop->initialize(unsat, sat); TODO
	if(!sat && !unsat){
		getSolver()->addSet(this);
		for(int i=0; i<getAgg().size(); i++){
			if(getAgg()[i]->isDefined()){
				getSolver()->getPCSolver()->notifyAggrHead(var(getAgg()[i]->getHead()));
			}
		}
	}*/
}

// Final initialization call!
void Propagator::initialize(bool& unsat, bool& sat) {
	for (int i = 0; i < getSet().getAgg().size(); i++) {
		getSolver()->setHeadWatch(var(getSet().getAgg()[i]->getHead()), getSet().getAgg()[i]);
	}
}

///////
// HELP METHODS
///////

AggSolver* Propagator::getSolver() {
	return getSet().getSolver();
}

rClause Propagator::notifySolver(AggReason* reason){
	return getSolver()->notifySolver(reason);
}

lbool Propagator::value(const Lit& l) const {
	return getSolver()->value(l);
}

///////
// TRANSFORMATIONS
///////

bool Aggrs::compareWLByLits(const WL& one, const WL& two) {
	return var(one.getLit()) < var(two.getLit());
}

vector<TypedSet*> Aggrs::transformSetReduction(TypedSet* const set){
	assert(set->getType()!=NULL);

	vwl oldset = set->getWL();
	vwl newset;

	//Sort all wlits according to the integer representation of their literal (to get all literals next to each other)
	std::sort(oldset.begin(), oldset.end(), compareLits);

	int indexinnew = 0;
	newset.push_back(oldset[indexinnew]);

	bool setisreduced = false;
	for (vwl::size_type i = 1; i < oldset.size(); i++) {
		WL oldl = newset[indexinnew];
		WL newl = oldset[i];
		if (var(oldl.getLit()) == var(newl.getLit())) { //same variable
			setisreduced = true;
			if (oldl.getLit() == newl.getLit()) { //same literal, keep combined weight
				Weight w = set->getType()->getCombinedWeight(newl.getWeight(), oldl.getWeight());
				newset[indexinnew] = WL(oldl.getLit(), w);
			} else { //opposite signs
				WL wl = set->getType()->handleOccurenceOfBothSigns(oldl, newl);
				newset[indexinnew] = WL(wl.getLit(), wl.getWeight());
			}
		} else {
			newset.push_back(newl);
			indexinnew++;
		}
	}

	vwl newset2;
	for (vwl::size_type i = 0; i < newset.size(); i++) {
		if (!isNeutralElement(newset[i].getWeight())) {
			newset2.push_back(newset[i]);
		} else {
			setisreduced = true;
		}
	}

	if (setisreduced) {
		set->setWL(newset2);
	}
}

void Aggrs::transformSumsToCNF(bool& unsat, map<int, TypedSet*>& parsedsets, PCSolver* pcsolver){
/*	int sumaggs = 0;
	int maxvar = 1;
	vector<PBAgg*> pbaggs;
	for (map<int, TypedSet*>::const_iterator i = parsedsets.begin(); i != parsedsets.end(); i++) {
		vpagg remaining;
		for(int j=0; j<(*i).second->getAgg().size(); j++){
			Agg* agg = (*i).second->getAgg()[j];
			if(!agg->isOptim() && (agg->getType()==SUM || agg->getType()==CARD) && !agg->getSem()==DEF){
				PBAgg* ppbaggeq = new PBAgg();
				PBAgg* ppbaggineq = new PBAgg();
				pbaggs.push_back(ppbaggeq);
				pbaggs.push_back(ppbaggineq);
				PBAgg& pbaggeq = *ppbaggeq;
				PBAgg& pbaggineq = *ppbaggineq;
				if(agg->getSign()==LB){
					pbaggeq.sign = -1;
					pbaggineq.sign = 2;
				}else{
					pbaggeq.sign = 1;
					pbaggineq.sign = -2;
				}
				pbaggeq.bound = agg->getBound();
				pbaggineq.bound = agg->getBound();
				Weight min = 0, max = 0;
				for(vwl::const_iterator k=(*i).second->getWL().begin(); k<(*i).second->getWL().end(); k++){
					pbaggeq.literals.push(MiniSatPP::Lit(var((*k).getLit()), sign((*k).getLit())));
					pbaggineq.literals.push(MiniSatPP::Lit(var((*k).getLit()), sign((*k).getLit())));
					if(var((*k).getLit())>maxvar){
						maxvar = var((*k).getLit());
					}
					if((*k).getWeight()<0){
						min += (*k).getWeight();
					}else{
						max += (*k).getWeight();
					}
					pbaggeq.weights.push(MiniSatPP::Int((int)((*k).getWeight())));
					pbaggineq.weights.push(MiniSatPP::Int((int)((*k).getWeight())));
				}
				if(var(agg->getHead())>maxvar){
					maxvar = var(agg->getHead());
				}
				pbaggeq.literals.push(MiniSatPP::Lit(var(agg->getHead()), true));
				pbaggineq.literals.push(MiniSatPP::Lit(var(agg->getHead()), false));
				Weight eqval, ineqval;
				if(agg->getSign()==LB){
					eqval = -abs(agg->getBound())-abs(max)-1;
					ineqval = abs(agg->getBound())+abs(min)+1;
				}else{
					eqval = abs(agg->getBound())+abs(min)+1;
					ineqval = -abs(agg->getBound())-abs(max)-1;
				}
				//report("Eqval=%d, ineqval=%d, maxvar=%d\n", eqval, ineqval, maxvar);
				pbaggeq.weights.push(MiniSatPP::Int(eqval));
				pbaggineq.weights.push(MiniSatPP::Int(ineqval));
			}else{
				remaining.push_back(agg);
			}
		}
		(*i).second->getAgg().clear();
		(*i).second->getAgg().insert((*i).second->getAgg().begin(), remaining.begin(), remaining.end());
	}

	MiniSatPP::PbSolver* pbsolver = new MiniSatPP::PbSolver();
	MiniSatPP::opt_verbosity = pcsolver->modes().verbosity;
	MiniSatPP::opt_abstract = true; //Should be true
	MiniSatPP::opt_tare = true; //Experimentally set to true
	MiniSatPP::opt_primes_file = pcsolver->modes().primesfile;
	MiniSatPP::opt_convert_weak = false;
	MiniSatPP::opt_convert = MiniSatPP::ct_Mixed;
	pbsolver->allocConstrs(maxvar, sumaggs);

	for(vector<PBAgg*>::const_iterator i=pbaggs.begin(); !unsat && i<pbaggs.end(); i++){
		unsat = !pbsolver->addConstr((*i)->literals, (*i)->weights, (*i)->bound, (*i)->sign, false);
	}
	deleteList<PBAgg>(pbaggs);

	if(unsat){
		delete pbsolver;
		return;
	}

	//get CNF out of the pseudoboolean matrix
	vector<vector<MiniSatPP::Lit> > pbencodings;
	unsat = !pbsolver->toCNF(pbencodings);
	delete pbsolver;
	if(unsat){
		return;
	}

	//Any literal that is larger than maxvar will have been newly introduced, so should be mapped to nVars()+lit
	//add the CNF to the solver
	int maxnumber = pcsolver->nVars();
	for(vector<vector<MiniSatPP::Lit> >::const_iterator i=pbencodings.begin(); i<pbencodings.end(); i++){
		vec<Lit> lits;
		for(vector<MiniSatPP::Lit>::const_iterator j=(*i).begin(); j<(*i).end(); j++){
			Var v = MiniSatPP::var(*j) + (MiniSatPP::var(*j)>maxvar?maxnumber-maxvar:0);
			lits.push(mkLit(v, MiniSatPP::sign(*j)));
		}
		pcsolver->addClause(lits);
	}*/
}
