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
#include <iostream>

#include "theorysolvers/PCSolver.hpp"
#include "datastructures/InternalAdd.hpp"
#include "utils/Utils.hpp"
#include "utils/Print.hpp"

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
	// Represents the level of some atom in binary representation
	// First bit is 2^0
	varlist bits_;
public:
	template<class Solver>
	Level2SAT(Var head, Solver& solver, int maxlevel){
		int maxbits = (log((double)maxlevel)/log(2))+0.5;
		if(solver.verbosity()>4){
			std::clog <<"loopsize = " <<maxlevel <<", maxbits = " <<maxbits <<"\n";
		}
		for(int i=0; i<maxbits; ++i) {
			auto var = solver.newVar();
			if(solver.verbosity()>4){
				std::clog <<toString(mkPosLit(var), solver) <<" <=> " <<"l(" <<toString(mkPosLit(head), solver) <<")>=" <<pow(2, i) <<"\n";
			}
			bits_.push_back(var);
		}
	}

	// The full list of bits
	const varlist& bits() const { return bits_; }

	// Represents level 0
	litlist zero() const { return zero(bits_.size()-1); }

	// Represents a level which has the first <toindex> bits set to 0
	litlist zero(int toindex) const {
		litlist list;
		for(auto i=0; i<toindex+1; ++i){
			list.push_back(mkNegLit(bits()[i]));
		}
		return list;
	}

	// Represents a level which has the first <toindex> bits set to 1
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
	enum class SIGN { L1, G}; // L1 = LorEqual+1, G = Greater

	// Represents a comparison "level op level"
	struct Comp{
		SIGN sign;
		Level2SAT *left, *right;

		Comp(Level2SAT* left, SIGN sign, Level2SAT* right): sign(sign), left(left), right(right){}

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
	};

	// Represents that the level of some atom == 0
	struct EqToZero{
		Level2SAT* left;
		bool operator== (const EqToZero& enc) const { return left==enc.left; }
		bool operator< (const EqToZero& enc) const { return left<enc.left; }
		EqToZero(Level2SAT* left):left(left){}
	};

private:
	Solver& solver_;
	std::map<Var, Level2SAT*> atom2level;

	// Ensures that only one literal is generated for some equality
	std::map<EqToZero,Lit> eq2zeromap;
	std::map<Comp,Lit> largermap;

public:
	// @pre: rules is one SCC
	SCCtoCNF(Solver& solver):solver_(solver){}

	SATVAL transform(const std::vector<Rule*>& rules){
		std::set<Var> defined;
		if(solver_.verbosity()>4){
			std::clog <<"SCC to transform to CNF: ";
		}
		for(auto rule=rules.cbegin(); rule!=rules.cend(); ++rule){
			if(solver_.verbosity()>4){
				std::clog <<toString(mkPosLit((*rule)->getHead()), solver_) <<" ";
			}
			defined.insert((*rule)->getHead());
		}
		if(solver_.verbosity()>4){
			std::clog <<"\n";
		}

		for(auto head=defined.cbegin(); head!=defined.cend(); ++head){
			auto headvar = new Level2SAT(*head, solver_, defined.size()); // maxlevel is the scc size
			atom2level[*head] = headvar;

			if(solver_.value(mkPosLit(*head))==l_True){
				continue;
			}

			// Encode ~p => l(p)=0 for all non-true defineds
			addClause(litlist{mkPosLit(*head), zero2SAT(headvar)});
		}

		// existence of a level is encoded implicitly

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
	// NOTE: STRONG encoding is always used!
	/*
	 * P <- Q1 | ... | Qn
	 * ==>
	 * if P true and some open true, then level is 0 ==> ~P | ~O | l(P)=0
	 * if P true and all opens false, then some def is true and P > level def
	 * if P is true and def true, then level head =< def+1
	 */
	SATVAL transformDisjunction(const Rule& rule){
		auto head = mkPosLit(rule.getHead());
		if(solver_.value(head)==l_False){
			return solver_.satState();
		}

		auto headvar = atom2level[rule.getHead()];

		litlist tseitins{~head};
		for(auto litit = rule.def().cbegin(); litit!=rule.def().cend(); ++litit) {
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
	 * P <- Q1 & ... & Qn
	 * ==>
	 * if P true, then level is higher than all defs and equal to the highest of them + 1
	 */
	SATVAL transformConjunction(const Rule& rule){
		auto headvar = atom2level[rule.getHead()];
		Lit head = mkPosLit(rule.getHead());

		if(solver_.value(head)==l_False){
			return solver_.satState();
		}

		litlist tseitins{~head};
		for(auto litit = rule.def().cbegin(); litit!=rule.def().cend(); ++litit) {
			auto bodyvar = atom2level[var(*litit)];

			addClause(litlist{~head, Comp2SAT(headvar, SIGN::G, bodyvar)});
			tseitins.push_back(Comp2SAT(headvar, SIGN::L1, bodyvar));
			// FIXME should check returned literals on their value!
		}
		tseitins.push_back(zero2SAT(headvar));

		addClause(tseitins);

		return solver_.satState();
	}

	// FIXME use current interpretation to simplify things in the code below

	Lit Comp2SAT(Level2SAT* left, SIGN sign, Level2SAT* right){
		auto it = largermap.find(Comp(left, sign, right));
		if(it==largermap.cend()){
			Lit tseitin;
			MAssert(left->bits().size()==right->bits().size());
			if(sign==SIGN::G){
				tseitin = G2SAT(left, right, left->bits().size()-1);
			}else{
				tseitin = L12SAT(left, right, left->bits().size()-1);
			}
			largermap[Comp(left, sign, right)] = tseitin;
			return tseitin;
		}else{
			return (*it).second;
		}
	}

	Lit L12SAT(Level2SAT* left, Level2SAT* right, int index){
		MAssert(left->bits().size()>index && right->bits().size()>index);
		if(index==0){
			return solver_.getTrueLit();
		}else if(index==1){
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
						L12SAT(left, right, index-1)
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
		MAssert(left->bits().size()>index && right->bits().size()>index);
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

	SATVAL addClause(const litlist& lits){
		internalAdd(Disjunction(lits), solver_);
		return solver_.satState();
	}

	// Returns a literal which represents that the level of the var is 0
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
		if(subs.size()==1){
			return subs.back();
		}
		bool alltrue = true;
		for(auto i=subs.cbegin(); i<subs.cend(); ++i){
			auto val = solver_.rootValue(*i);
			if(val==l_Undef){
				alltrue = false;
			}else if(val==l_False){
				return solver_.getFalseLit();
			}
		}
		if(alltrue){
			return solver_.getTrueLit();
		}
		auto tseitin = mkPosLit(solver_.newVar());
		internalAdd(Implication(tseitin, ImplicationType::EQUIVALENT, subs, true), solver_);
		return tseitin;
	}

	Lit or2SAT(const litlist& subs){
		if(subs.size()==1){
			return subs.back();
		}
		bool allfalse = true;
		for(auto i=subs.cbegin(); i<subs.cend(); ++i){
			auto val = solver_.rootValue(*i);
			if(val==l_Undef){
				allfalse = false;
			}else if(val==l_True){
				return solver_.getTrueLit();
			}
		}
		if(allfalse){
			return solver_.getFalseLit();
		}
		auto tseitin = mkPosLit(solver_.newVar());
		internalAdd(Implication(tseitin, ImplicationType::EQUIVALENT, subs, false), solver_);
		return tseitin;
	}
};

template<class Solver>
bool transformSCCtoCNF(Solver& solver, std::vector<Rule*>& rules){
	auto transformer = new SCCtoCNF<Solver>(solver);
	auto state = transformer->transform(rules);
	delete transformer;
	return state!=SATVAL::UNSAT;
}

}

} /* namespace MinisatID */
#endif /* SCCtoCNF_HPP_ */
