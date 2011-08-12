/************************************
 SCC2SAT.hpp
 this file belongs to GidL 2.0
 (c) K.U.Leuven
 ************************************/

#ifndef SCC2SAT_HPP_
#define SCC2SAT_HPP_

#include <vector>
#include <cmath>

#include "utils/Utils.hpp"

namespace MinisatID {

class SCC2SAT {
	class Rule{
		bool disjunctive_;
		Var head_;
		std::vector<Var> defbody_;
		std::vector<Lit> openbody_;

	public:
		Var getHead() const { return head_; }
		bool isDisjunctive() const { return disjunctive_; }
		const std::vector<Var>& defVars() const { return defbody_; }
		const std::vector<Lit>& openLits() const { return openbody_; }
	};

	class LevelVar{
		// First bit is 2^0
		std::vector<Var> bits_;
	public:
		LevelVar(PCSolver& solver, int maxlevel){
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
private:
	PCSolver* solver_;
	int maxlevel;
	std::map<Var, LevelVar*> atom2level;
	std::set<Var> defined;
	typedef std::pair<Encoding, Var> enc2var;
	std::map<Encoding, Var> necessaryEncodings;
	std::map<UnaryEncoding, Var> necessaryUnEncodings;
public:
	// @pre: rules is one SCC
	void transform(PCSolver* solver, const std::vector<Rule*>& rules){
		solver_ = solver;
		for(auto rule=rules.begin(); rule!=rules.end(); ++rule){
			defined.insert((*rule)->getHead());
		}
		maxlevel = defined.size()-1; // maxlevel is the scc size - 1
		for(auto head=defined.begin(); head!=defined.end(); ++head){
			atom2level.insert(std::pair<Var, LevelVar*>(*head, new LevelVar(*solver, maxlevel)));
		}
		for(auto rule=rules.begin(); rule!=rules.end(); ++rule){
			if((*rule)->isDisjunctive()){
				transformDisjunction(**rule);
			}else{
				transformConjunction(**rule);
			}
		}
	}

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
	void transformDisjunction(const Rule& rule){
		LevelVar* headvar = atom2level[rule.getHead()];
		InnerDisjunction tseitins;
		tseitins.literals.push(mkNegLit(rule.getHead()));
		for(auto def = rule.defVars().begin(); def!=rule.defVars().end(); ++def){
			LevelVar* bodyvar = atom2level[*def];
			InnerDisjunction clause;
			clause.literals.push(mkNegLit(rule.getHead()));
			clause.literals.push(mkNegLit(*def));
			clause.literals.push(retrieveEncoding(headvar, bodyvar, ENC_LEQPLUS1));
			solver_->add(clause);

			Var tseitin = solver_->newVar();
			tseitins.literals.push(mkPosLit(tseitin));

			InnerEquivalence eq;
			eq.head = mkPosLit(tseitin);
			eq.conjunctive = true;
			eq.literals.push(mkPosLit(*def));
			eq.literals.push(retrieveEncoding(headvar, bodyvar, ENC_GREATER));
		}
		for(auto open = rule.openLits().begin(); open!=rule.openLits().end(); ++open){
			InnerDisjunction clause;
			clause.literals.push(mkNegLit(rule.getHead()));
			clause.literals.push(not *open);
			clause.literals.push(retrieveEncoding(headvar, ENC_LEQPLUS1));
			solver_->add(clause);

			Var tseitin = solver_->newVar();
			tseitins.literals.push(mkPosLit(tseitin));

			InnerEquivalence eq;
			eq.head = mkPosLit(tseitin);
			eq.conjunctive = true;
			eq.literals.push(*open);
			eq.literals.push(retrieveEncoding(headvar, ENC_GREATER));
		}
		solver_->add(tseitins);
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
	void transformConjunction(const Rule& rule){
		LevelVar* headvar = atom2level[rule.getHead()];
		InnerDisjunction tseitins;
		tseitins.literals.push(mkNegLit(rule.getHead()));
		for(auto def = rule.defVars().begin(); def!=rule.defVars().end(); ++def){
			LevelVar* bodyvar = atom2level[*def];
			InnerDisjunction clause;
			clause.literals.push(mkNegLit(rule.getHead()));
			clause.literals.push(retrieveEncoding(headvar, bodyvar, ENC_GREATER));
			solver_->add(clause);

			Var tseitin = solver_->newVar();
			tseitins.literals.push(mkPosLit(tseitin));

			InnerEquivalence eq;
			eq.head = mkPosLit(tseitin);
			eq.conjunctive = true;
			eq.literals.push(mkPosLit(*def));
			eq.literals.push(retrieveEncoding(headvar, bodyvar, ENC_LEQPLUS1));
		}
		if(rule.openLits().size()>0){
			InnerDisjunction clause;
			clause.literals.push(mkNegLit(rule.getHead()));
			clause.literals.push(retrieveEncoding(headvar, ENC_GREATER));
			solver_->add(clause);
		}
		for(auto open = rule.openLits().begin(); open!=rule.openLits().end(); ++open){
			Var tseitin = solver_->newVar();
			tseitins.literals.push(mkPosLit(tseitin));

			InnerEquivalence eq;
			eq.head = mkPosLit(tseitin);
			eq.conjunctive = true;
			eq.literals.push(*open);
			eq.literals.push(retrieveEncoding(headvar, ENC_LEQPLUS1));
		}
		solver_->add(tseitins);
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
				v = solver_->newVar();
				InnerEquivalence eq;
				eq.head = mkPosLit(v);
				eq.conjunctive = true;
				for(auto bit=++left->bits().begin(); bit!=left->bits().end(); ++bit){
					eq.literals.push(mkNegLit(*bit));
				}
				solver_->add(eq);
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

	Lit addEq(const Lit& leftbit, const Lit& rightbit){
		InnerEquivalence neq;
		neq.head = mkPosLit(solver_->newVar());
		neq.conjunctive = true;
		neq.literals.push(leftbit);
		neq.literals.push(rightbit);
		solver_->add(neq);
		return neq.head;
	}

	Lit addEq(const Lit& one, const Lit& two, const Lit& three){
		InnerEquivalence neq;
		neq.head = mkPosLit(solver_->newVar());
		neq.conjunctive = true;
		neq.literals.push(one);
		neq.literals.push(two);
		neq.literals.push(three);
		solver_->add(neq);
		return neq.head;
	}

	/*
		level encoding:
		l(P1) = 2^0*P11 + 2^1*P12 + ... + 2^max*P1max
		encode leq+1 as
		TODO
		leqp1(P1, Q1, i) <=> P1i<Q1i | (P1i=Q1i & leqp1(P1, Q1, i-1))
		leqp1(P1, Q1, 0) <=> true
		then l(P1)=<l(Q1)+1 becomes leqp1(P1, Q1, max)
		encode greater as
		g(P1, Q1, i) <=> (P1i & ~Q1i) | (P1i & Q1i & g(P1, Q1, i-1)) | (~P1i & ~Q1i & g(P1, Q1, i-1))
		g(P1, Q1, 0) <=> P10 & ~Q10
		then l(P1)>l(Q1) becomes g(P1, Q1, max)
	*/
	Var addEncoding(const Encoding& enc){
		Var next;
		if(enc.sign == ENC_GREATER){
			Var prev = solver_->newVar();
			InnerEquivalence eq;
			eq.head = mkPosLit(prev);
			eq.conjunctive = true;
			eq.literals.push(mkPosLit(enc.left->bits()[0]));
			eq.literals.push(mkNegLit(enc.right->bits()[0]));
			solver_->add(eq);
			for(int i=1; i<enc.left->bits().size(); ++i){
				next = solver_->newVar();
				Var leftbit = enc.left->bits()[i];
				Var rightbit = enc.right->bits()[i];
				InnerEquivalence eq;
				eq.head = mkPosLit(next);
				eq.conjunctive = false;
				eq.literals.push(addEq(mkPosLit(leftbit), mkNegLit(rightbit)));
				eq.literals.push(addEq(mkPosLit(leftbit), mkPosLit(rightbit), mkPosLit(prev)));
				eq.literals.push(addEq(mkNegLit(leftbit), mkNegLit(rightbit), mkPosLit(prev)));
				solver_->add(eq);
				prev = next;
			}
		}else{
			// TODO
		}
		necessaryEncodings.insert(enc2var(enc, next));
		return next;
	}
};

} /* namespace MinisatID */
#endif /* SCC2SAT_HPP_ */
