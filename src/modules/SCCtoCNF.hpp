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

#include "modules/SCCtoCNF.hpp"
#include "theorysolvers/PCSolver.hpp"
#include "utils/Utils.hpp"

namespace MinisatID {

namespace toCNF{

class Rule{
	bool disjunctive_;
	Var head_;
	std::vector<Var> defbody_;
	litlist openbody_;

public:
	Rule(bool disjunctive, Var head, const std::vector<Var>& deflits, const litlist& openlits)
			:disjunctive_(disjunctive), head_(head), defbody_(deflits), openbody_(openlits){

	}

	Var getHead() const { return head_; }
	bool isDisjunctive() const { return disjunctive_; }
	const std::vector<Var>& defVars() const { return defbody_; }
	const litlist& openLits() const { return openbody_; }
};

class LevelVar{
	// First bit is 2^0
	std::vector<Var> bits_;
public:
	template<class Solver>
	LevelVar(Solver& solver, int maxlevel){
		int maxbits = (log((double)maxlevel)/log(2))+0.5;
		for(int i=0; i<maxbits; ++i) {
			bits_.push_back(solver.newVar());
		}
	}

	const std::vector<Var> bits() const { return bits_; }
};

enum ENC_SIGN { ENC_LEQPLUS1, ENC_GREATER };

struct Encoding{
	LevelVar *left, *right;
	ENC_SIGN sign;
		// if true: left =< right + 1
		// else left > right

	bool operator== (const Encoding& enc) const {
		return left==enc.left || right==enc.right || sign==enc.sign;
	}
	bool operator< (const Encoding& enc) const {
		return left<enc.left || right<enc.right || sign<enc.sign;
	}

	Encoding(LevelVar* left, LevelVar* right, ENC_SIGN sign)
			:left(left), right(right), sign(sign){

	}
};

struct UnaryEncoding{
	LevelVar *left;
	ENC_SIGN sign;
		// if true: left =<  1
		// else left > 0

	bool operator== (const UnaryEncoding& enc) const {
		return left==enc.left || sign==enc.sign;
	}
	bool operator< (const UnaryEncoding& enc) const {
		return left<enc.left || sign<enc.sign;
	}

	UnaryEncoding(LevelVar* left, ENC_SIGN sign)
			:left(left), sign(sign){
	}
};

template<class Solver>
class SCCtoCNF {
private:
	Solver& solver_;
	int maxlevel;
	std::map<Var, LevelVar*> atom2level;
	std::set<Var> defined;
	typedef std::pair<Encoding, Var> enc2var;
	std::map<Encoding, Var> necessaryEncodings;
	std::map<UnaryEncoding, Var> necessaryUnEncodings;
public:

	// @pre: rules is one SCC
	SCCtoCNF(Solver& solver):solver_(solver){}

	SATVAL transform(const std::vector<Rule*>& rules){
		for(auto rule=rules.begin(); rule!=rules.end(); ++rule){
			defined.insert((*rule)->getHead());
		}
		maxlevel = defined.size(); // maxlevel is the scc size
		for(auto head=defined.begin(); head!=defined.end(); ++head){
			atom2level.insert(std::pair<Var, LevelVar*>(*head, new LevelVar(solver_, maxlevel)));
		}
		SATVAL state = SATVAL::POS_SAT;
		for(auto rule=rules.begin(); state==SATVAL::POS_SAT && rule!=rules.end(); ++rule){
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
	 * P1 => l(P1) = min(l(Q1)|Q1, ..., l(Qn)|Qn)+1
	 * ==>
	 * P1 & Q1 => l(P1)=<l(Q1)+1
	 * ...
	 * P1 & Qn => l(P1)=<l(Qn)+1
	 * P1 => (l(P1)>=l(Q1)+1 & Q1) | ... (l(P1)>=l(Qn)+1 & Qn)
	 * ==>
	 * ==>
	 * ~P1 | ~Q1 | l(P1)=<l(Q1)+1
	 * ...
	 * ~P1 | ~Qn | l(P1)=<l(Qn)+1
	 * ~P1 | PT1 | ... | PTn
	 * PT1 <=> l(P1)>l(Q1) & Q1
	 * ...
	 * PTn <=> l(P1)>l(Qn) & Qn
	 */
	SATVAL transformDisjunction(const Rule& rule){
		SATVAL state = SATVAL::POS_SAT;
		LevelVar* headvar = atom2level[rule.getHead()];
		InnerDisjunction tseitins;
		tseitins.literals.push_back(mkNegLit(rule.getHead()));
		for(auto def = rule.defVars().begin(); def!=rule.defVars().end(); ++def) {
			if(state!=SATVAL::POS_SAT){
		    	break;
		    }
			assert(defined.find(*def)!=defined.end());
			LevelVar* bodyvar = atom2level[*def];
			state &= addClause(litlist{mkNegLit(rule.getHead()), mkNegLit(*def), retrieveEncoding(headvar, bodyvar, ENC_LEQPLUS1)});

			Lit tseitin = mkPosLit(solver_.newVar());
			tseitins.literals.push_back(tseitin);
			state &= addConjEq(tseitin, litlist{mkPosLit(*def), retrieveEncoding(headvar, bodyvar, ENC_GREATER)});
		}
		for(auto open = rule.openLits().begin(); open!=rule.openLits().end(); ++open) {
			if(state!=SATVAL::POS_SAT){
		    	break;
		    }
			state &= addClause(litlist{mkNegLit(rule.getHead()), not *open, retrieveEncoding(headvar, ENC_LEQPLUS1)});

			Lit tseitin = mkPosLit(solver_.newVar());
			tseitins.literals.push_back(tseitin);
			state &= addConjEq(tseitin, litlist{*open, retrieveEncoding(headvar, ENC_GREATER)});
		}
		solver_.add(tseitins);
		state &= solver_.isUnsat();
		return state;
	}

	/*
	 * 	Q1 <- P1 & ... & Qn
	 * 	==>
	 * 	Q1 => l(Q1) = max(l(P1)|P1, ..., l(Pn)|Pn)+1
	 * 	==>
	 * 	Q1 => l(Q1)>=l(P1)+1
	 * 	...
	 * 	Q1 => l(Q1)>=l(Pn)+1
	 * 	Q1 => (l(Q1)=<l(P1)+1 & P1) | ... (l(Q1)<=l(Pn)+1 & Pn)
	 * 	==>
	 * 	~Q1 | l(Q1)>l(P1)
	 * 	...
	 * 	~Q1 | l(Q1)>l(Pn)
	 * 	~Q1 | QT1 | ... | QTn
	 * 	QT1 <=> l(Q1)=<l(P1)+1 & P1
	 * 	...
	 * 	QTn <=> l(Q1)<=l(Pn)+1 & Pn
	 */
	SATVAL transformConjunction(const Rule& rule){
		SATVAL state = SATVAL::POS_SAT;
		LevelVar* headvar = atom2level[rule.getHead()];
		InnerDisjunction tseitins;
		tseitins.literals.push_back(mkNegLit(rule.getHead()));
		for(auto def = rule.defVars().begin(); state==SATVAL::POS_SAT && def!=rule.defVars().end(); ++def){
			assert(defined.find(*def)!=defined.end());
			LevelVar* bodyvar = atom2level[*def];
			state &= addClause(litlist{mkNegLit(rule.getHead()), retrieveEncoding(headvar, bodyvar, ENC_GREATER)});

			Lit tseitin = mkPosLit(solver_.newVar());
			tseitins.literals.push_back(tseitin);
			state &= addConjEq(tseitin, litlist{mkPosLit(*def), retrieveEncoding(headvar, bodyvar, ENC_LEQPLUS1)});
		}
		if(rule.openLits().size()>0){
			state &= addClause(litlist{mkNegLit(rule.getHead()), retrieveEncoding(headvar, ENC_GREATER)});
		}
		for(auto open = rule.openLits().begin(); state==SATVAL::POS_SAT && open!=rule.openLits().end(); ++open){
			Lit tseitin = mkPosLit(solver_.newVar());
			tseitins.literals.push_back(tseitin);
			state &= addConjEq(tseitin, litlist{*open, retrieveEncoding(headvar, ENC_LEQPLUS1)});
		}
		solver_.add(tseitins);
		state &= solver_.isUnsat();
		return state;
	}

	bool isOpen(const Lit& lit){
		return sign(lit) || defined.find(var(lit))==defined.end();
	}

	// Retrieve encoding of left > 0 (left[1]=1) or left <= 1 (left[i]=0 forall i except lowest)
	// level van alle atomen tussen 0 en maxlevel (inclusief). opens hebben level 0 (dus geen level encoding nodig)
	Lit retrieveEncoding(LevelVar* left, ENC_SIGN sign){
		if(sign==ENC_GREATER){
			return mkPosLit(left->bits()[0]);
		}else{
			auto enc = necessaryUnEncodings.find(UnaryEncoding(left, sign));
			Var v;
			if(enc==necessaryUnEncodings.end()){
				v = solver_.newVar();
				InnerEquivalence eq;
				eq.head = mkPosLit(v);
				eq.conjunctive = true;
				for(auto bit=++left->bits().begin(); bit!=left->bits().end(); ++bit){
					eq.literals.push_back(mkNegLit(*bit));
				}
				solver_.add(eq);
				necessaryUnEncodings.insert(std::pair<UnaryEncoding, Var>(UnaryEncoding(left, sign), v));
			}else{
				v = enc->second;
			}
			return mkPosLit(v);
		}
	}

	Lit retrieveEncoding(LevelVar* left, LevelVar* right, ENC_SIGN sign){
		auto enc = necessaryEncodings.find(Encoding(left, right, sign));
		Var v;
		if(enc==necessaryEncodings.end()){
			v = addEncoding(Encoding(left, right, sign));
		}else{
			v = enc->second;
		}
		return mkPosLit(v);
	}

	SATVAL addClause(const litlist& lits){
		InnerDisjunction d;
		d.literals = lits;
		solver_.add(d);
		return solver_.isUnsat();
	}

	SATVAL addDisjEq(const Lit& head, const litlist& lits){
		InnerEquivalence eq;
		eq.head = head;
		eq.conjunctive = false;
		eq.literals = lits;
		solver_.add(eq);
		return solver_.isUnsat();
	}

	SATVAL addConjEq(const Lit& head, const litlist& lits){
		InnerEquivalence eq;
		eq.head = head;
		eq.conjunctive = true;
		eq.literals = lits;
		solver_.add(eq);
		return solver_.isUnsat();
	}

	/*
		level encoding:
		l(P1) = 2^0*P11 + 2^1*P12 + ... + 2^max*P1max
		encode leq+1 as
		fullft(P1, Q1, i) <=> ~P1i & Q1i & fullft(P1, Q1, i-1)
		leqp1(P1, Q1, i) <=> (~P1i & Q1i) | (P10 & Q10 & leqp1(P1, Q1, i-1)) | (~P10 & ~Q10 & leqp1(P1, Q1, i-1)) | (P11 & ~Q11 & fullft(P1, Q1, i-1))
		leqp1(P1, Q1, 1) <=> ~(~Q11 & ~Q10 & P11 & P10)
		then l(P1)=<l(Q1)+1 becomes leqp1(P1, Q1, max)
		encode greater as
		g(P1, Q1, i) <=> (P1i & ~Q1i) | (P1i & Q1i & g(P1, Q1, i-1)) | (~P1i & ~Q1i & g(P1, Q1, i-1))
		g(P1, Q1, 0) <=> P10 & ~Q10
		then l(P1)>l(Q1) becomes g(P1, Q1, max)
	*/
	Var addEncoding(const Encoding& enc){
		Var next;
		SATVAL state = SATVAL::POS_SAT;
		if(enc.sign == ENC_GREATER){
			// greater base case: g(P1,Q1,0) <=> P10 & ~Q10
			Var prev = solver_.newVar();
			Var leftbiti = enc.left->bits()[0];
			Var rightbiti = enc.right->bits()[0];
			state &= addConjEq(mkPosLit(prev), litlist{mkPosLit(leftbiti), mkNegLit(rightbiti)});

			// greater recursive case
			for(vsize i=1; i<enc.left->bits().size(); ++i){
				Var leftbit = enc.left->bits()[i];
				Var rightbit = enc.right->bits()[i];
				Lit firstconj = mkPosLit(solver_.newVar());
				state &= addConjEq(firstconj, litlist{mkPosLit(leftbit), mkNegLit(rightbit)});
				Lit secondconj = mkPosLit(solver_.newVar());
				state &= addConjEq(secondconj, litlist{mkPosLit(leftbit), mkPosLit(rightbit), mkPosLit(prev)});
				Lit thirdconj = mkPosLit(solver_.newVar());
				state &= addConjEq(thirdconj, litlist{mkNegLit(leftbit), mkNegLit(rightbit), mkPosLit(prev)});

				next = solver_.newVar();
				state &= addDisjEq(mkPosLit(next), litlist{firstconj, secondconj, thirdconj});
				prev = next;
			}
		}else{
			//leqp1(P1, Q1, 0) <=> true
			if(enc.left->bits().size()<2){
				next = solver_.newVar();
				state &= addClause(litlist{mkPosLit(next)});
			}else{
				//fullft(P1, Q1, i) <=> ~P1i & Q1i & fullft(P1, Q1, i-1)
				std::vector<Var> fullfalstrue;
				Lit temp = mkPosLit(solver_.newVar());
				state &= addConjEq(temp, litlist{mkNegLit(enc.left->bits()[0]), mkPosLit(enc.right->bits()[0])});
				Var prev = var(temp);
				fullfalstrue.push_back(prev);
				for(vsize i=1; i<enc.left->bits().size(); ++i){
					next = solver_.newVar();
					Var leftbit = enc.left->bits()[i];
					Var rightbit = enc.right->bits()[i];
					state &= addConjEq(mkPosLit(next), litlist{mkNegLit(leftbit), mkPosLit(rightbit), mkPosLit(prev)}); // TODO return value
					prev = next;
					fullfalstrue.push_back(prev);
				}

				//leqp1(P1, Q1, i) <=> (~P1i & Q1i) | (P10 & Q10 & leqp1(P1, Q1, i-1)) | (~P10 & ~Q10 & leqp1(P1, Q1, i-1)) | (P11 & ~Q11 & fullft(P1, Q1, i-1))
				//leqp1(P1, Q1, 1) <=> ~(~Q11 & ~Q10 & P11 & P10)
				prev = solver_.newVar();
				state &= addConjEq(mkNegLit(prev), litlist{mkNegLit(enc.right->bits()[1]),mkNegLit(enc.right->bits()[0]), mkPosLit(enc.left->bits()[1]), mkPosLit(enc.left->bits()[0])});

				for(vsize i=1; i<enc.left->bits().size(); ++i){
					Var leftbit = enc.left->bits()[i];
					Var rightbit = enc.right->bits()[i];

					Lit firstconj = mkPosLit(solver_.newVar());
					state &= addConjEq(firstconj, litlist{mkNegLit(leftbit), mkPosLit(rightbit)});
					Lit secondconj = mkPosLit(solver_.newVar());
					state &= addConjEq(secondconj, litlist{mkPosLit(leftbit), mkPosLit(rightbit), mkPosLit(prev)});
					Lit thirdconj = mkPosLit(solver_.newVar());
					state &= addConjEq(thirdconj, litlist{mkNegLit(leftbit), mkNegLit(rightbit), mkPosLit(prev)});
					Lit fourthconj = mkPosLit(solver_.newVar());
					state &= addConjEq(fourthconj, litlist{mkPosLit(leftbit), mkNegLit(rightbit), mkPosLit(fullfalstrue[i-1])});

					next = solver_.newVar();
					state &= addDisjEq(mkPosLit(next), litlist{firstconj, secondconj, thirdconj, fourthconj});
					prev = next;
				}
			}
		}
		assert(state == SATVAL::POS_SAT);
		necessaryEncodings.insert(enc2var(enc, next));
		return next;
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
