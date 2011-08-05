#ifndef INTVAR_HPP
#define INTVAR_HPP

#include <vector>
#include "utils/Utils.hpp"
#include "theorysolvers/PCSolver.hpp"

namespace MinisatID{

class IntVar{
	PCSolver& engine;
	int offset, minvalue, maxvalue;
	std::vector<Var> equalities;	// eq[atom-off] == minvalue+i
	std::vector<Var> disequalities; // eq[atom-off] =< minvalue+i
	
	IntVar(PCSolver& engine, int min, int max): engine(engine), offset(engine.nVars()), minvalue(min), maxvalue(max){
		for(int i=min; i<max+1; ++i){
			equalities.push_back(engine.newVar());
			disequalities.push_back(engine.newVar());
		}
		addConstraints(engine);
	}

	int minValue(){
		for(uint i=0; i<equalities.size(); ++i){
			if(engine.value(equalities[i])!=l_False){
				return minvalue+i;
			}
		}
		assert(false);
	}

	int maxValue(){
		for(uint i=equalities.size()-1; i>=0; --i){
			if(engine.value(equalities[i])!=l_False){
				return minvalue+i;
			}
		}
		assert(false);
	}

private:
	void addConstraints(){
		InnerSet set;
		set.setID = engine.nextSetID();
		for(uint i=0; i<equalities.size(); ++i){
			set.literals.push_back(engine.newVar());
		}
		InnerAggregate lowercard;
		lowercard.setID = set.setID;
		lowercard.bound = 1;
		lowercard.type = CARD;
		lowercard.sign = AGGSIGN_LB;
		InnerAggregate highercard(lowercard);
		highercard.sign = AGGSIGN_UB;
		engine.add(set);
		engine.add(highercard);
		engine.add(lowercard);
		// TODO miss propagation in other direction?
		for(uint i=0; i<equalities.size(); ++i){
			// if eq[i] => diseq[i]
			InnerDisjunction same;
			same.literals.push(mkNegLit(equalities[i]));
			same.literals.push(mkPosLit(disequalities[i]));
			engine.add(same);
			if(i<equalities.size()-1){
				// if eq[i] => ~diseq[i+1]
				InnerDisjunction next;
				next.literals.push(mkNegLit(equalities[i]));
				next.literals.push(mkNegLit(disequalities[i+1]));
				engine.add(next);
				// if ~diseq[i] => ~diseq[i+1]
				InnerDisjunction nextdis;
				nextdis.literals.push(mkPosLit(disequalities[i]));
				nextdis.literals.push(mkNegLit(disequalities[i+1]));
				engine.add(nextdis);
			}
			// if diseq[i] => diseq[i-1]
			if(i>0){
				InnerDisjunction prev;
				prev.literals.push(mkNegLit(disequalities[i]));
				prev.literals.push(mkPosLit(disequalities[i-1]));
				engine.add(prev);
			}
		}
	}
};

}

#endif //INTVAR_HPP
