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

IntVar::IntVar(PCSolver* solver, int _origid, int min, int max)
		: Propagator(solver, "intvar"),
		  id_(maxid_++), origid_(_origid),
		  engine_(*solver),
		  minvalue(min), maxvalue(max),
		  offset(-1), currentmin(min), currentmax(max){
	getPCSolver().accept(this, EV_BACKTRACK);
	getPCSolver().accept(this, EV_PROPAGATE);

	for(int i=origMinValue(); i<origMaxValue()+1; ++i){
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
			std::clog <<toString(*i) <<" <=> " <<origid() <<"=" <<minvalue+index <<"\n";
		}
		index = 0;
		for(auto i=disequalities.cbegin(); i<disequalities.cend(); ++i, index++){
			std::clog <<toString(*i) <<" <=> " <<origid() <<"=<" <<minvalue+index <<"\n";
		}
	}
	std::clog <<"var" <<origid() <<"[" <<currentmin <<"," <<currentmax <<"]\n";
	getPCSolver().acceptBounds(new IntView(this, 0), this);
}

void IntVar::notifyBacktrack(int, const Lit&){
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
	std::clog <<"var" <<origid() <<"[" <<currentmin <<"," <<currentmax <<"] (post-backtrack)\n";
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
		std::clog <<"var" <<origid() <<"[" <<currentmin <<"," <<currentmax <<"]\n";
		engine().notifyBoundsChanged(this);
	}

	return nullPtrClause;
}

void IntVar::addConstraints(){
	WLSet set;
	set.setID = engine().newSetID();
	for(uint i=0; i<equalities.size(); ++i){
		set.wl.push_back(WLtuple(mkPosLit(equalities[i]), 1));
	}
	Aggregate lowercard(engine().newVar(), set.setID, 1, AggType::CARD, AggSign::LB, AggSem::COMP, -1);
	Aggregate highercard(lowercard);
	highercard.head = engine().newVar();
	highercard.sign = AggSign::UB;
	engine().add(set);
	engine().add(Disjunction({mkPosLit(highercard.head)}));
	engine().add(Disjunction({mkPosLit(lowercard.head)}));
	engine().add(highercard);
	engine().add(lowercard);
	// TODO do we miss propagation in other direction?
	for(uint i=0; i<equalities.size(); ++i){
		// if eq[i] => diseq[i]
		Disjunction same;
		same.literals.push_back(mkNegLit(equalities[i]));
		same.literals.push_back(mkPosLit(disequalities[i]));
		engine().add(same);
		if(i<equalities.size()-1){
			// if diseq[i] => diseq[i+1]
			Disjunction prev;
			prev.literals.push_back(mkNegLit(disequalities[i]));
			prev.literals.push_back(mkPosLit(disequalities[i+1]));
			engine().add(prev);
		}
		if(i>0){
			// if eq[i] => ~diseq[i-1]
			Disjunction next;
			next.literals.push_back(mkNegLit(equalities[i]));
			next.literals.push_back(mkNegLit(disequalities[i-1]));
			engine().add(next);
			// if ~diseq[i] => ~diseq[i-1]
			Disjunction nextdis;
			nextdis.literals.push_back(mkPosLit(disequalities[i]));
			nextdis.literals.push_back(mkNegLit(disequalities[i-1]));
			engine().add(nextdis);
		}
	}
}
