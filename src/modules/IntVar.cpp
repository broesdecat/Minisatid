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

IntVar::IntVar(PCSolver* solver, int origid, int min, int max)
		: Propagator(solver),
		  id_(maxid_++), origid_(origid),
		  engine_(*solver), offset(engine().nVars()),
		  minvalue(min), maxvalue(max),
		  currentmin(min), currentmax(max){
	getPCSolver().accept(this, EV_BACKTRACK);
	getPCSolver().accept(this, EV_PROPAGATE);
	getPCSolver().acceptFinishParsing(this, false);
}

void IntVar::finishParsing(bool& present, bool& unsat){
	for(int i=origMinValue(); i<origMaxValue()+1; ++i){
		equalities.push_back(engine().newVar());
		disequalities.push_back(engine().newVar());
	}
	for(auto i=equalities.begin(); i<equalities.end(); ++i){
		engine().acceptLitEvent(this, mkPosLit(*i), FAST);
		engine().acceptLitEvent(this, mkNegLit(*i), FAST);
	}
	for(auto i=disequalities.begin(); i<disequalities.end(); ++i){
		engine().acceptLitEvent(this, mkPosLit(*i), FAST);
		engine().acceptLitEvent(this, mkNegLit(*i), FAST);
	}
	addConstraints();
	engine().notifyBoundsChanged(this);

	if(verbosity()>3){
		int index = 0;
		for(auto i=equalities.begin(); i<equalities.end(); ++i, index++){
			std::clog <<mkPosLit(*i) <<" <=> " <<origid() <<"=" <<minvalue+index <<"\n";
		}
		index = 0;
		for(auto i=disequalities.begin(); i<disequalities.end(); ++i, index++){
			std::clog <<mkPosLit(*i) <<" <=> " <<origid() <<"=<" <<minvalue+index <<"\n";
		}
	}
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
		if(engine().value(equalities[index])!=l_False){
			currentmax = minvalue + index;
		}
	}
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
		engine().notifyBoundsChanged(this);
	}

	return nullPtrClause;
}

void IntVar::addConstraints(){
	InnerSet set;
	set.setID = engine().newSetID();
	for(uint i=0; i<equalities.size(); ++i){
		set.literals.push_back(mkPosLit(equalities[i]));
	}
	// FIXME this happens after finishparsing of the factory (and possible also after finishing the aggsolver), so these are NOT added
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
		same.literals.push(mkNegLit(equalities[i]));
		same.literals.push(mkPosLit(disequalities[i]));
		engine().add(same);
		if(i<equalities.size()-1){
			// if eq[i] => ~diseq[i+1]
			InnerDisjunction next;
			next.literals.push(mkNegLit(equalities[i]));
			next.literals.push(mkNegLit(disequalities[i+1]));
			engine().add(next);
			// if ~diseq[i] => ~diseq[i+1]
			InnerDisjunction nextdis;
			nextdis.literals.push(mkPosLit(disequalities[i]));
			nextdis.literals.push(mkNegLit(disequalities[i+1]));
			engine().add(nextdis);
		}
		// if diseq[i] => diseq[i-1]
		if(i>0){
			InnerDisjunction prev;
			prev.literals.push(mkNegLit(disequalities[i]));
			prev.literals.push(mkPosLit(disequalities[i-1]));
			engine().add(prev);
		}
	}
}
