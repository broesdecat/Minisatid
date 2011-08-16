/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */

#include <vector>
#include <cmath>

#include "modules/SCCtoCNF.hpp"
#include "theorysolvers/PCSolver.hpp"

namespace MinisatID {

namespace toCNF{

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

enum SATENUM { POSSIBLYSAT, UNSAT };

class SCCtoCNF {
private:
	PCSolver& solver_;
	int maxlevel;
	std::map<Var, LevelVar*> atom2level;
	std::set<Var> defined;
	typedef std::pair<Encoding, Var> enc2var;
	std::map<Encoding, Var> necessaryEncodings;
	std::map<UnaryEncoding, Var> necessaryUnEncodings;
public:

	// @pre: rules is one SCC
	SCCtoCNF(PCSolver& solver):solver_(solver){}

	SATENUM transform(const std::vector<Rule*>& rules){
		for(auto rule=rules.begin(); rule!=rules.end(); ++rule){
			defined.insert((*rule)->getHead());
		}
		maxlevel = defined.size(); // maxlevel is the scc size
		for(auto head=defined.begin(); head!=defined.end(); ++head){
			atom2level.insert(std::pair<Var, LevelVar*>(*head, new LevelVar(solver_, maxlevel)));
		}
		SATENUM state = POSSIBLYSAT;
		for(auto rule=rules.begin(); state==POSSIBLYSAT && rule!=rules.end(); ++rule){
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
	SATENUM transformDisjunction(const Rule& rule){
		SATENUM state = POSSIBLYSAT;
		LevelVar* headvar = atom2level[rule.getHead()];
		InnerDisjunction tseitins;
		tseitins.literals.push(mkNegLit(rule.getHead()));
		for(auto def = rule.defVars().begin(); state==POSSIBLYSAT && def!=rule.defVars().end(); ++def){
			assert(defined.find(*def)!=defined.end());
			LevelVar* bodyvar = atom2level[*def];
			InnerDisjunction clause;
			clause.literals.push(mkNegLit(rule.getHead()));
			clause.literals.push(mkNegLit(*def));
			clause.literals.push(retrieveEncoding(headvar, bodyvar, ENC_LEQPLUS1));
			if(not solver_.add(clause)){
				state = UNSAT;
			}

			Var tseitin = solver_.newVar();
			tseitins.literals.push(mkPosLit(tseitin));

			InnerEquivalence eq;
			eq.head = mkPosLit(tseitin);
			eq.conjunctive = true;
			eq.literals.push(mkPosLit(*def));
			eq.literals.push(retrieveEncoding(headvar, bodyvar, ENC_GREATER));
			if(not solver_.add(eq)){
				state = UNSAT;
			}
		}
		for(auto open = rule.openLits().begin(); state==POSSIBLYSAT && open!=rule.openLits().end(); ++open){
			InnerDisjunction clause;
			clause.literals.push(mkNegLit(rule.getHead()));
			clause.literals.push(not *open);
			clause.literals.push(retrieveEncoding(headvar, ENC_LEQPLUS1));
			if(not solver_.add(clause)){
				state = UNSAT;
			}

			Var tseitin = solver_.newVar();
			tseitins.literals.push(mkPosLit(tseitin));

			InnerEquivalence eq;
			eq.head = mkPosLit(tseitin);
			eq.conjunctive = true;
			eq.literals.push(*open);
			eq.literals.push(retrieveEncoding(headvar, ENC_GREATER));
			if(not solver_.add(eq)){
				state = UNSAT;
			}
		}
		if(not solver_.add(tseitins)){
			state = UNSAT;
		}
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
	SATENUM transformConjunction(const Rule& rule){
		SATENUM state = POSSIBLYSAT;
		LevelVar* headvar = atom2level[rule.getHead()];
		InnerDisjunction tseitins;
		tseitins.literals.push(mkNegLit(rule.getHead()));
		for(auto def = rule.defVars().begin(); state==POSSIBLYSAT && def!=rule.defVars().end(); ++def){
			assert(defined.find(*def)!=defined.end());
			LevelVar* bodyvar = atom2level[*def];
			InnerDisjunction clause;
			clause.literals.push(mkNegLit(rule.getHead()));
			clause.literals.push(retrieveEncoding(headvar, bodyvar, ENC_GREATER));
			if(not solver_.add(clause)){
				state = UNSAT;
			}

			Var tseitin = solver_.newVar();
			tseitins.literals.push(mkPosLit(tseitin));

			InnerEquivalence eq;
			eq.head = mkPosLit(tseitin);
			eq.conjunctive = true;
			eq.literals.push(mkPosLit(*def));
			eq.literals.push(retrieveEncoding(headvar, bodyvar, ENC_LEQPLUS1));
			if(not solver_.add(eq)){
				state = UNSAT;
			}
		}
		if(rule.openLits().size()>0){
			InnerDisjunction clause;
			clause.literals.push(mkNegLit(rule.getHead()));
			clause.literals.push(retrieveEncoding(headvar, ENC_GREATER));
			if(not solver_.add(clause)){
				state = UNSAT;
			}
		}
		for(auto open = rule.openLits().begin(); state==POSSIBLYSAT && open!=rule.openLits().end(); ++open){
			Var tseitin = solver_.newVar();
			tseitins.literals.push(mkPosLit(tseitin));

			InnerEquivalence eq;
			eq.head = mkPosLit(tseitin);
			eq.conjunctive = true;
			eq.literals.push(*open);
			eq.literals.push(retrieveEncoding(headvar, ENC_LEQPLUS1));
			if(not solver_.add(eq)){
				state = UNSAT;
			}
		}
		if(not solver_.add(tseitins)){
			state = UNSAT;
		}
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
					eq.literals.push(mkNegLit(*bit));
				}
				bool possiblysat = solver_.add(eq);
				assert(possiblysat);
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
		neq.head = mkPosLit(solver_.newVar());
		neq.conjunctive = true;
		neq.literals.push(leftbit);
		neq.literals.push(rightbit);
		solver_.add(neq); // cannot become unsat
		return neq.head;
	}

	Lit addEq(const Lit& one, const Lit& two, const Lit& three){
		InnerEquivalence neq;
		neq.head = mkPosLit(solver_.newVar());
		neq.conjunctive = true;
		neq.literals.push(one);
		neq.literals.push(two);
		neq.literals.push(three);
		solver_.add(neq);  // cannot become unsat
		return neq.head;
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
		SATENUM state = POSSIBLYSAT;
		if(enc.sign == ENC_GREATER){
			Var prev = solver_.newVar();
			InnerEquivalence eq;
			eq.head = mkPosLit(prev);
			eq.conjunctive = true;
			eq.literals.push(mkPosLit(enc.left->bits()[0]));
			eq.literals.push(mkNegLit(enc.right->bits()[0]));
			if(not solver_.add(eq)){
				state = UNSAT;
			}
			for(int i=1; i<enc.left->bits().size(); ++i){
				next = solver_.newVar();
				Var leftbit = enc.left->bits()[i];
				Var rightbit = enc.right->bits()[i];
				InnerEquivalence eq;
				eq.head = mkPosLit(next);
				eq.conjunctive = false;
				eq.literals.push(addEq(mkPosLit(leftbit), mkNegLit(rightbit)));
				eq.literals.push(addEq(mkPosLit(leftbit), mkPosLit(rightbit), mkPosLit(prev)));
				eq.literals.push(addEq(mkNegLit(leftbit), mkNegLit(rightbit), mkPosLit(prev)));
				if(not solver_.add(eq)){
					state = UNSAT;
				}
				prev = next;
			}
		}else{
			//leqp1(P1, Q1, 0) <=> true
			if(enc.left->bits().size()<2){
				next = solver_.newVar();
				InnerDisjunction d;
				d.literals.push(mkPosLit(next));
				solver_.add(d);  // cannot become unsat
			}else{
				//fullft(P1, Q1, i) <=> ~P1i & Q1i & fullft(P1, Q1, i-1)
				std::vector<Var> fullfalstrue;
				Var prev = var(addEq(mkNegLit(enc.left->bits()[0]), mkPosLit(enc.right->bits()[0])));
				fullfalstrue.push_back(prev);
				for(int i=1; i<enc.left->bits().size(); ++i){
					next = solver_.newVar();
					Var leftbit = enc.left->bits()[i];
					Var rightbit = enc.right->bits()[i];
					InnerEquivalence eq;
					eq.head = mkPosLit(next);
					eq.conjunctive = true;
					eq.literals.push(mkNegLit(leftbit));
					eq.literals.push(mkPosLit(rightbit));
					eq.literals.push(mkPosLit(prev));
					if(not solver_.add(eq)){
						state = UNSAT;
					}
					prev = next;
					fullfalstrue.push_back(prev);
				}

				//leqp1(P1, Q1, i) <=> (~P1i & Q1i) | (P10 & Q10 & leqp1(P1, Q1, i-1)) | (~P10 & ~Q10 & leqp1(P1, Q1, i-1)) | (P11 & ~Q11 & fullft(P1, Q1, i-1))
				//leqp1(P1, Q1, 1) <=> ~(~Q11 & ~Q10 & P11 & P10)
				InnerEquivalence eq;
				prev = solver_.newVar();
				eq.head = mkNegLit(prev);
				eq.conjunctive = true;
				eq.literals.push(mkNegLit(enc.right->bits()[1]));
				eq.literals.push(mkNegLit(enc.right->bits()[0]));
				eq.literals.push(mkPosLit(enc.left->bits()[1]));
				eq.literals.push(mkPosLit(enc.left->bits()[0]));
				if(not solver_.add(eq)){
					state = UNSAT;
				}
				for(int i=1; i<enc.left->bits().size(); ++i){
					next = solver_.newVar();
					Var leftbit = enc.left->bits()[i];
					Var rightbit = enc.right->bits()[i];
					InnerEquivalence eq;
					eq.head = mkPosLit(next);
					eq.conjunctive = true;
					eq.literals.push(addEq(mkNegLit(leftbit), mkPosLit(rightbit)));
					eq.literals.push(addEq(mkPosLit(leftbit), mkPosLit(rightbit), mkPosLit(prev)));
					eq.literals.push(addEq(mkNegLit(leftbit), mkNegLit(rightbit), mkPosLit(prev)));
					eq.literals.push(addEq(mkPosLit(leftbit), mkNegLit(rightbit), mkPosLit(fullfalstrue[i-1])));
					if(not solver_.add(eq)){
						state = UNSAT;
					}
					prev = next;
				}
			}
		}
		assert(state == POSSIBLYSAT);
		necessaryEncodings.insert(enc2var(enc, next));
		return next;
	}
};

bool transformSCCtoCNF(PCSolver& solver, const std::vector<Rule*>& rules){
	SCCtoCNF* scc2cnf = new SCCtoCNF(solver);
	SATENUM state = scc2cnf->transform(rules);
	return state==POSSIBLYSAT;
}

}

} /* namespace MinisatID */
