/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef SCCtoCNF_HPP_
#define SCCtoCNF_HPP_

#include <vector>
#include <cmath>

#include "theorysolvers/PCSolver.hpp"
#include "utils/Utils.hpp"

namespace MinisatID {

namespace toCNF{

class Rule{
	bool disjunctive_;
	Var head_;
	litlist defbody_, openbody_;

public:
	Rule(bool disjunctive, Var head, const litlist& deflits, const litlist& openlits)
			:disjunctive_(disjunctive), head_(head), defbody_(deflits), openbody_(openlits){}

	Var 			getHead() 		const { return head_; }
	bool 			isDisjunctive() const { return disjunctive_; }
	const litlist& 	def() 			const { return defbody_; }
	const litlist& 	open() 			const { return openbody_; }
};

class Level2SAT{
	// First bit is 2^0
	varlist bits_;
public:
	template<class Solver>
	Level2SAT(Solver& solver, int maxlevel){
		int maxbits = (log((double)maxlevel)/log(2))+0.5;
		for(int i=0; i<maxbits; ++i) {
			bits_.push_back(solver.newVar());
		}
	}

	const varlist& bits() const { return bits_; }
	litlist zero() const { return zero(bits_.size()-1); }
	litlist zero(int toindex) const {
		litlist list;
		for(auto i=0; i<toindex+1; ++i){
			list.push_back(mkNegLit(bits()[i]));
		}
		return list;
	}

	litlist one(int toindex) const {
		litlist list;
		for(auto i=0; i<toindex+1; ++i){
			list.push_back(mkPosLit(bits()[i]));
		}
		return list;
	}
};

template<class Solver>
class SCCtoCNF {
	enum class SIGN { L1, G};

	struct Comp{
		SIGN sign;
		Level2SAT *left, *right;
		bool operator== (const Comp& enc) const {
			return sign==enc.sign && left==enc.left && right==enc.right;
		}
		bool operator< (const Comp& enc) const {
			if(sign==SIGN::L1 && enc.sign==SIGN::G){
				return true;
			}else if(sign==SIGN::G && enc.sign==SIGN::L1){
				return false;
			}else{
				return left<enc.left || (left==enc.left && right<enc.right);
			}
		}
		Comp(Level2SAT* left, SIGN sign, Level2SAT* right): sign(sign), left(left), right(right){}
	};

	struct EqToZero{
		Level2SAT* left;
		bool operator== (const EqToZero& enc) const { return left==enc.left; }
		bool operator< (const EqToZero& enc) const { return left<enc.left; }
		EqToZero(Level2SAT* left):left(left){}
	};

private:
	Solver& solver_;
	int maxlevel;
	std::map<Var, Level2SAT*> atom2level;
	std::set<Var> defined;
	std::map<EqToZero,Lit> eq2zeromap;
	std::map<Comp,Lit> largermap;
public:

	// @pre: rules is one SCC
	SCCtoCNF(Solver& solver):solver_(solver){}

	SATVAL transform(const std::vector<Rule*>& rules){
		for(auto rule=rules.cbegin(); rule!=rules.cend(); ++rule){
			defined.insert((*rule)->getHead());
		}

		maxlevel = defined.size(); // maxlevel is the scc size

		for(auto head=defined.cbegin(); head!=defined.cend(); ++head){
			auto headvar = new Level2SAT(solver_, maxlevel);
			atom2level[*head] = headvar;

			// Encode ~p => l(p)=0 for all defineds
			if(solver_.value(*head)!=l_True){
				addClause(litlist{mkPosLit(*head), zero2SAT(headvar)});
			}
		}

		SATVAL state = SATVAL::POS_SAT;
		for(auto rule=rules.cbegin(); state==SATVAL::POS_SAT && rule!=rules.cend(); ++rule){
			if((*rule)->isDisjunctive()){
				state = transformDisjunction(**rule);
			}else{
				state = transformConjunction(**rule);
			}
		}
		return state;
	}

private:
	/*
	 * P1 <- Q1 | ... | Qn
	 * ==>
	 * !def i: ~P | l(P)=<l(Qi)+1 | ~Qi
	 * !open i: ~P | l(P)=0 | ~Qi
	 * ~P | (l(P)>l(Q1) & Q1) | ... | (l(P)>l(Qn) & Qn) or def qi: =0
	 */
	SATVAL transformDisjunction(const Rule& rule){
		auto headvar = atom2level[rule.getHead()];
		Lit head = mkPosLit(rule.getHead());

		if(solver_.value(head)==l_False){
			return solver_.satState();
		}

		litlist tseitins{~head};
		for(auto litit = rule.def().cbegin(); litit!=rule.def().cend(); ++litit) {
			assert(defined.find(var(*litit))!=defined.cend());
			auto bodyvar = atom2level[var(*litit)];

			if(solver_.value(*litit)!=l_False){
				addClause(litlist{~head, ~(*litit), Comp2SAT(headvar, SIGN::L1, bodyvar)});
				tseitins.push_back(and2SAT(litlist{*litit, Comp2SAT(headvar, SIGN::G, bodyvar)}));
				// FIXME should check returned literals on their value!
			}
		}

		for(auto litit = rule.open().cbegin(); litit!=rule.open().cend(); ++litit) {
			if(solver_.value(*litit)!=l_False){
				addClause(litlist{~head, ~(*litit), zero2SAT(headvar)});
				tseitins.push_back(and2SAT(litlist{*litit, zero2SAT(headvar)}));
				// FIXME should check returned literals on their value!
			}
		}

		addClause(tseitins);

		return solver_.satState();
	}

	/*
	 * P1 <- Q1 & ... & Qn
	 * ==>
	 * !def i: ~P | l(P)>l(Qi)
	 * ~P | l(P)=<l(Q1)+1 | ... | l(P)=<l(Qn)+1 only for qi in def
	 */
	SATVAL transformConjunction(const Rule& rule){
		auto headvar = atom2level[rule.getHead()];
		Lit head = mkPosLit(rule.getHead());

		if(solver_.value(head)==l_False){
			return solver_.satState();
		}

		litlist tseitins{~head};
		for(auto litit = rule.def().cbegin(); litit!=rule.def().cend(); ++litit) {
			assert(defined.find(var(*litit))!=defined.cend());
			auto bodyvar = atom2level[var(*litit)];

			addClause(litlist{~head, Comp2SAT(headvar, SIGN::G, bodyvar)});
			tseitins.push_back(Comp2SAT(headvar, SIGN::L1, bodyvar));
			// FIXME should check returned literals on their value!
		}
		tseitins.push_back(zero2SAT(headvar));

		addClause(tseitins);

		return solver_.satState();
	}

	// FIXME use current interpretation to simplify things in the code below also

	SATVAL addClause(const litlist& lits){
		InnerDisjunction d;
		d.literals = lits;
		solver_.add(d);
		return solver_.satState();
	}

	Lit zero2SAT(Level2SAT* left){
		auto it = eq2zeromap.find(EqToZero(left));
		if(it==eq2zeromap.cend()){
			Lit tseitin = and2SAT(left->zero());
			eq2zeromap[EqToZero(left)] = tseitin;
			return tseitin;
		}else{
			return (*it).second;
		}
	}

	Lit and2SAT(const litlist& subs){
		Lit tseitin = mkPosLit(solver_.newVar());

		InnerEquivalence eq;
		eq.head = tseitin;
		eq.conjunctive = true;
		eq.literals = subs;
		solver_.add(eq);

		return tseitin;
	}

	Lit or2SAT(const litlist& subs){
		Lit tseitin = mkPosLit(solver_.newVar());

		InnerEquivalence eq;
		eq.head = tseitin;
		eq.conjunctive = false;
		eq.literals = subs;
		solver_.add(eq);

		return tseitin;
	}

	Lit Comp2SAT(Level2SAT* left, SIGN sign, Level2SAT* right){
		auto it = largermap.find(Comp(left, sign, right));
		if(it==largermap.cend()){
			Lit tseitin;
			if(sign==SIGN::G){
				tseitin = G2SAT(left, right, left->bits().size());
			}else{
				tseitin = L2SAT(left, right, left->bits().size());
			}
			largermap[Comp(left, sign, right)] = tseitin;
			return tseitin;
		}else{
			return (*it).second;
		}
	}

	Lit L2SAT(Level2SAT* left, Level2SAT* right, int index){
		if(index==1){
			return ~and2SAT(litlist{
						mkPosLit(left->bits()[0]),
						mkPosLit(left->bits()[0]),
						mkNegLit(right->bits()[1]),
						mkNegLit(right->bits()[0])
					});
		}else{
			return or2SAT(litlist{
					and2SAT(litlist{
						EqBit2SAT(right->bits()[index], left->bits()[index]),
						L2SAT(left, right, index-1)
					}),
					and2SAT(litlist{
						GBit2SAT(right->bits()[index], left->bits()[index]),
						restZero2SAT(right, index-1),
						restOneSAT(left, index-1)
					})
				});
		}
	}

	Lit restZero2SAT(Level2SAT* left, int index){
		litlist list(left->zero(index));
		return and2SAT(list);
	}

	Lit restOneSAT(Level2SAT* left, int index){
		litlist list(left->one(index));
		return and2SAT(list);
	}

	Lit G2SAT(Level2SAT* left, Level2SAT* right, int index){
		Lit gtseitin = GBit2SAT(left->bits()[0], right->bits()[0]);
		if(index==0){
			return gtseitin;
		}else{
			return or2SAT(litlist{
					gtseitin,
					and2SAT(litlist{
						EqBit2SAT(left->bits()[index], right->bits()[index]),
						G2SAT(left, right, index-1)})});
		}
	}

	Lit GBit2SAT(Var leftbit, Var rightbit){
		return and2SAT(litlist{mkPosLit(leftbit), mkNegLit(rightbit)});
	}

	Lit EqBit2SAT(Var leftbit, Var rightbit){
		return or2SAT(litlist{
						and2SAT(litlist{mkPosLit(leftbit), mkPosLit(rightbit)}),
						and2SAT(litlist{mkNegLit(leftbit), mkNegLit(rightbit)})});
	}
};

template<class Solver>
bool transformSCCtoCNF(Solver& solver, std::vector<Rule*>& rules){
	SCCtoCNF<Solver>* transformer = new SCCtoCNF<Solver>(solver);
	SATVAL state = transformer->transform(rules);
	delete transformer;
	return state!=SATVAL::UNSAT;
}

}

} /* namespace MinisatID */
#endif /* SCCtoCNF_HPP_ */
