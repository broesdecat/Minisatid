/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */

#include "modules/IntVar.hpp"
#include <iostream>
#include "utils/Print.hpp"

using namespace MinisatID;

std::map<int, IntVarValue> IntVar::var2intvarvalues;

IntVar::IntVar(PCSolver* solver, int origid, int min, int max)
		: Propagator(solver),
		  id_(maxid_++), origid_(origid),
		  engine_(*solver),
		  minvalue(min), maxvalue(max),
		  offset(-1), currentmin(min), currentmax(max){
	getPCSolver().accept(this, EV_BACKTRACK);
	getPCSolver().accept(this, EV_PROPAGATE);
	getPCSolver().acceptFinishParsing(this, false);
}

void IntVar::finishParsing(bool& present, bool& unsat){
	offset = engine().nVars();
	for(int i=origMinValue(); i<origMaxValue()+1; ++i){
		// TODO equalities moeten mss geen decision vars zijn?
		Var var = engine().newVar();
		equalities.push_back(var);
		var2intvarvalues.insert(std::pair<int, IntVarValue>(var, IntVarValue(this, true, i+minValue())));

		var = engine().newVar();
		disequalities.push_back(var);
		var2intvarvalues.insert(std::pair<int, IntVarValue>(var, IntVarValue(this, false, i+minValue())));

	}
	for(auto i=equalities.cbegin(); i<equalities.cend(); ++i){
		engine().accept(this, mkPosLit(*i), FAST);
		engine().accept(this, mkNegLit(*i), FAST);
	}
	for(auto i=disequalities.cbegin(); i<disequalities.cend(); ++i){
		engine().accept(this, mkPosLit(*i), FAST);
		engine().accept(this, mkNegLit(*i), FAST);
	}
	addConstraints();
	engine().notifyBoundsChanged(this);

	if(verbosity()>3){
		int index = 0;
		for(auto i=equalities.cbegin(); i<equalities.cend(); ++i, index++){
			std::clog <<mkPosLit(*i) <<" <=> " <<origid() <<"=" <<minvalue+index <<"\n";
		}
		index = 0;
		for(auto i=disequalities.cbegin(); i<disequalities.cend(); ++i, index++){
			std::clog <<mkPosLit(*i) <<" <=> " <<origid() <<"=<" <<minvalue+index <<"\n";
		}
	}
	std::cerr <<"var" <<origid() <<"[" <<currentmin <<"," <<currentmax <<"]\n";
	getPCSolver().acceptBounds(new IntView(this, 0), this);
}

void IntVar::notifyBacktrack(int untillevel, const Lit& decision){
	for(uint i=0; i<equalities.size(); ++i){
		if(engine().value(equalities[i])!=l_False){
			currentmin = minvalue+i;
			break;
		}
	}
	uint index = equalities.size()-1;
	for(auto i=equalities.rbegin(); i<equalities.rend(); ++i, --index){
		if(engine().value(*i)!=l_False){
			currentmax = minvalue + index;
			break;
		}
	}
	std::cerr <<"var" <<origid() <<"[" <<currentmin <<"," <<currentmax <<"] (post-backtrack)\n";
}

rClause	IntVar::notifypropagate(){
	int lastmin = currentmin, lastmax = currentmax;
	for(uint i=0; i<equalities.size(); ++i){
		if(engine().value(equalities[i])!=l_False){
			currentmin = minvalue+i;
			break;
		}
	}
	uint index = equalities.size()-1;
	for(auto i=equalities.rbegin(); i<equalities.rend(); ++i, --index){
		if(engine().value(equalities[index])!=l_False){
			currentmax = minvalue + index;
			break;
		}
	}
	if(lastmin!=currentmin || lastmax!=currentmax){
		std::cerr <<"var" <<origid() <<"[" <<currentmin <<"," <<currentmax <<"]\n";
		engine().notifyBoundsChanged(this);
	}

	return nullPtrClause;
}

void IntVar::addConstraints(){
	InnerWLSet set(engine().newSetID(), std::vector<WL>());
	for(uint i=0; i<equalities.size(); ++i){
		set.wls.push_back(WL(mkPosLit(equalities[i]), 1));
	}
	InnerAggregate lowercard;
	lowercard.setID = set.setID;
	lowercard.bound = 1;
	lowercard.type = CARD;
	lowercard.sign = AGGSIGN_LB;
	InnerAggregate highercard(lowercard);
	highercard.sign = AGGSIGN_UB;
	engine().add(set);
	engine().add(highercard);
	engine().add(lowercard);
	// TODO miss propagation in other direction?
	for(uint i=0; i<equalities.size(); ++i){
		// if eq[i] => diseq[i]
		InnerDisjunction same;
		same.literals.push_back(mkNegLit(equalities[i]));
		same.literals.push_back(mkPosLit(disequalities[i]));
		engine().add(same);
		if(i<equalities.size()-1){
			// if diseq[i] => diseq[i+1]
			InnerDisjunction prev;
			prev.literals.push_back(mkNegLit(disequalities[i]));
			prev.literals.push_back(mkPosLit(disequalities[i+1]));
			engine().add(prev);
		}
		if(i>0){
			// if eq[i] => ~diseq[i-1]
			InnerDisjunction next;
			next.literals.push_back(mkNegLit(equalities[i]));
			next.literals.push_back(mkNegLit(disequalities[i-1]));
			engine().add(next);
			// if ~diseq[i] => ~diseq[i-1]
			InnerDisjunction nextdis;
			nextdis.literals.push_back(mkPosLit(disequalities[i]));
			nextdis.literals.push_back(mkNegLit(disequalities[i-1]));
			engine().add(nextdis);
		}
	}
}
