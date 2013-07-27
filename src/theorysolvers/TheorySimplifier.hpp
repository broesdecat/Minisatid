#pragma once

#include <string>
#include <sstream>
#include <queue>
#include "external/ConstraintVisitor.hpp"
#include "PropagatorFactory.hpp"

namespace MinisatID {

/**
 * Current code:
 * 		stores all constraints
 * 		saves all lit <=> var = bound
 * 				  lit <=> var =< bound
 * 		for the associated vars, the pcsolver does not make new literals, but reuses the heads of these.
 *
 * NOTE:
 * 		currently, disables propagation during parsing, which can be an issue for grounding.
 */
class TheorySimplifier: public Factory {
private:
	PropagatorFactory* factory;
	std::queue<Constraint*> constraints;
	std::map<Atom, std::set<Constraint*> > atom2constraints;
	std::map<VarID, std::set<Constraint*> > var2constraints;

	// only of the form H <=> VAR =< int and H <=> VAR = int
	// DO NOT make new atoms for these!!!
	std::map<VarID, std::map<Weight, Lit>> presentLEQcomps;
	std::map<VarID, std::map<Weight, Lit>> presentEQcomps;

	CPBinaryRel canonify(CPBinaryRel incomp) {
		auto temp = incomp;
		switch (incomp.rel) {
		case EqType::EQ:
			break;
		case EqType::NEQ:
			temp.head = ~temp.head;
			temp.rel = EqType::EQ;
			break;
		case EqType::LEQ:
			break;
		case EqType::GEQ:
			temp.head = ~temp.head;
			temp.bound -= 1;
			temp.rel = EqType::LEQ;
			break;
		case EqType::G:
			temp.head = ~temp.head;
			temp.rel = EqType::LEQ;
			break;
		case EqType::L:
			temp.bound -= 1;
			temp.rel = EqType::LEQ;
			break;
		}
		return temp;
	}

public:

	PropagatorFactory& getFactory() {
		return *factory;
	}

	// Return literal 0 if it does not exist yet.
	Lit exists(CPBinaryRel comp) {
		auto canoncomp = canonify(comp);
		if (canoncomp.rel == EqType::EQ) {
			auto it = presentEQcomps.find(canoncomp.varID);
			if (it == presentEQcomps.cend()) {
				return comp.head;
			}
			auto litit = it->second.find(canoncomp.bound);
			if (litit == it->second.cend()) {
				return comp.head;
			} else {
				return litit->second;
			}
		} else { // Leq
			auto it = presentLEQcomps.find(canoncomp.varID);
			if (it == presentLEQcomps.cend()) {
				return comp.head;
			}
			auto litit = it->second.find(canoncomp.bound);
			if (litit == it->second.cend()) {
				return comp.head;
			} else {
				return litit->second;
			}
		}
	}

	/**
	 * Internally created cp variables
	 * Equalities
	 * Equivalences
	 * Detected equivalences and equalities
	 *
	 * Idee:
	 * 	derive dat iets equal is (voeg niet toe als constraint)
	 * 		kijk of het overal geelimineerd kan worden
	 * 			zo ja, save constraint voor output
	 * 			zo nee, voeg equality expliciet nog toe
	 */

private:
	bool finished;

public:
	TheorySimplifier(PropagatorFactory* factory)
			: 	Factory("theorystorage"),
				factory(factory),
				finished(false) {

	}

	~TheorySimplifier() {
		delete (factory);
	}

	void includeCPModel(std::vector<VariableEqValue>& varassignments){
		return factory->includeCPModel(varassignments);
	}

	SATVAL finish() {
		finished = true;
		while (not constraints.empty()) {
			auto c = constraints.front();
			constraints.pop();
			c->accept(factory);
			delete (c);
		}
		return factory->finish();
	}

private:
	template<class T>
	void internalAdd(const T& obj) {
//		if(not ok) {
//			return;
//		}
		if (finished) {
			factory->add(obj);
			return;
		}
		constraints.push(new T(obj));
//		for(auto a: obj.getAtoms()) {
//			atom2constraints[a].insert(constraints.back());
//		}
	}

public:

	virtual void add(const Disjunction& obj) {
		internalAdd(obj);
	}
	virtual void add(const Implication& obj) {
		internalAdd(obj);
	}
	virtual void add(const Rule& obj) {
		internalAdd(obj);
	}
	virtual void add(const WLSet& obj) {
		internalAdd(obj);
	}
	virtual void add(const Aggregate& obj) {
		internalAdd(obj);
	}
	virtual void add(const MinimizeOrderedList& obj) {
		internalAdd(obj);
	}
	virtual void add(const MinimizeSubset& obj) {
		internalAdd(obj);
	}
	virtual void add(const MinimizeVar& obj) {
		internalAdd(obj);
	}
	virtual void add(const MinimizeAgg& obj) {
		internalAdd(obj);
	}
	virtual void add(const Symmetry& obj) {
		internalAdd(obj);
	}
	virtual void add(const BoolVar& obj) {
		internalAdd(obj);
	}
	virtual void add(const IntVarEnum& obj) {
		internalAdd(obj);
	}
	virtual void add(const IntVarRange& obj) {
		internalAdd(obj);
	}
	virtual void add(const CPAllDiff& obj) {
		internalAdd(obj);
	}
	virtual void add(const CPBinaryRel& obj);
	virtual void add(const CPCount& obj) {
		internalAdd(obj);
	}
	virtual void add(const CPBinaryRelVar& obj) {
		internalAdd(obj);
	}
	virtual void add(const CPSumWeighted& obj) {
		internalAdd(obj);
	}
	virtual void add(const CPProdWeighted& obj) {
		internalAdd(obj);
	}
	virtual void add(const CPElement& obj) {
		internalAdd(obj);
	}
	virtual void add(const LazyGroundLit& obj) {
		internalAdd(obj);
	}
	virtual void add(const LazyGroundImpl& obj) {
		internalAdd(obj);
	}
	virtual void add(const LazyAddition& obj) {
		internalAdd(obj);
	}
	virtual void add(const TwoValuedRequirement& obj) {
		internalAdd(obj);
	}
	virtual void add(const SubTheory&) {
		throw idpexception("Invalid code path");
	}
	virtual void add(const LazyAtom& obj) {
		internalAdd(obj);
	}

private:
	// FUTURE CODE
//	bool ok = true;
//	bool simplificationallowed = true;
//	std::map<Atom, bool> unitliterals;
//	std::map<Lit, Lit> equivs;
//	std::map<VarID, VarID> equalities;
//	std::map<Lit, std::pair<Lit, Lit> > potentialequivs;
//	std::map<Lit, std::pair<VarID, VarID> > potentialequalities;
//	void addUnit(Lit head) {
//		auto it = unitliterals.find(head.getAtom());
//		if (it != unitliterals.cend()) {
//			if ((it->second && head.hasSign()) || (not it->second && not head.hasSign())) {
//				ok = false;
//			}
//			return;
//		}
//		unitliterals[head.getAtom()] = not head.hasSign();
//		notifyLitCertainlyTrue(head);
//
//		auto& constr = atom2constraints[head.getAtom()];
//		for (auto i = constr.begin(); i < constr.end();) {
//			auto disj = dynamic_cast<Disjunction*>(*i);
//			if (disj == NULL) {
//				++i;
//				continue;
//			}
//			for (auto j = disj->literals.begin(); j < disj->literals.end();) {
//				if (same atom same sign) {
//					drop constraint
//				} else if (same atom different sign) {
//					remove literal
//				} else {
//					++j;
//				}
//			}
//			if (empty) {
//				unsat
//			} else if (unit) {
//				add to
//				unit
//			}
//		}
//		// TODO simplify other constraints
//	}
//
//	lbool rootValue(Lit lit) {
//		auto it = unitliterals.find(lit.getAtom());
//		if (it == unitliterals.cend()) {
//			return l_Undef;
//		} else {
//			return it->second ? l_True : l_False;
//		}
//	}
//
//	void add(Lit head, Lit left, Lit right) {
//		auto rootval = rootValue(head);
//		if (rootval == l_True) {
//			equivs[left] = right;
//		} else if (rootval != l_False) {
//			potentialequivs[head] = {left,right};
//		}
//	}
//
//	void add(Lit head, VarID left, VarID right) {
//		auto rootval = rootValue(head);
//		if(rootval==l_True) {
//			equalities[left] = right;
//		} else if(rootval!=l_False) {
//			potentialequalities[head] = {left,right};
//		}
//	}
//
//	void notifyLitCertainlyTrue(Lit lit) {
//		auto equalit = potentialequalities.find(lit);
//		if (equalit != potentialequalities.cend()) {
//			auto one = equalit->second.first, two = equalit->second.second;
//
//			auto existingoneit = equalities.find(one);
//			auto existingtwoit = equalities.find(two);
//			if(existingoneit!=equalities.cend()) {
//				equalities[two] = existingoneit->second;
//			} else if(existingtwoit!=equalities.cend()) {
//				equalities[one] = existingtwoit->second;
//			} else {
//				// TODO take one with smallest domain
//				equalities[one] = two;
//			}
//		}
//
//		auto equivit = potentialequivs.find(lit);
//		if (equivit != potentialequivs.cend()) {
//			auto one = equivit->second.first, two = equivit->second.second;
//
//			auto existingoneit = equivs.find(one);
//			auto existingtwoit = equivs.find(two);
//			if(existingoneit!=equivs.cend()) {
//				equivs[two] = existingoneit->second;
//			} else if(existingtwoit!=equivs.cend()) {
//				equivs[one] = existingtwoit->second;
//			} else {
//				if (rootValue(one) != l_Undef) {
//					equivs[two] = one;
//				} else {
//					equivs[one] = two;
//				}
//			}
//		}
//	}
};

}
