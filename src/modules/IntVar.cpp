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
#include "constraintvisitors/ConstraintVisitor.hpp"

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
		if(not isFalse(mkPosLit(equalities[i]))){
			currentmin = minvalue+i;
			break;
		}
	}
	uint index = equalities.size()-1;
	for(auto i=equalities.rbegin(); i<equalities.rend(); ++i, --index){
		if(not isFalse(mkPosLit(*i))){
			currentmax = minvalue + index;
			break;
		}
	}
	std::clog <<"var" <<origid() <<"[" <<currentmin <<"," <<currentmax <<"] (post-backtrack)\n";
}

void IntVar::accept(ConstraintVisitor& visitor){
	visitor.add(IntVarRange(origid(), minValue(), maxValue()));
}

rClause	IntVar::notifypropagate(){
	int lastmin = currentmin, lastmax = currentmax;
	for(uint i=0; i<equalities.size(); ++i){
		if(not isFalse(mkPosLit(equalities[i]))){
			currentmin = minvalue+i;
			break;
		}
	}
	uint index = equalities.size()-1;
	for(auto i=equalities.rbegin(); i<equalities.rend(); ++i, --index){
		if(not isFalse(mkPosLit(equalities[index]))){
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

/**
 * x in [min, max]
 * ?1 a: x>=a & x=<a
 * x=a then x>=a
 * x=a then x=<a
 *
 * x=<a then x=<a+1
 * ~x=<a then ~x=<a-1
 */
void IntVar::addConstraints(){
	auto setid = engine().newSetID();
	std::vector<WLtuple> wls;
	for(uint i=0; i<equalities.size(); ++i){
		wls.push_back(WLtuple(mkPosLit(equalities[i]), 1));
	}
	internalAdd(WLSet(setid, wls), engine());
	Aggregate lowercard(engine().newVar(), setid, 1, AggType::CARD, AggSign::LB, AggSem::COMP, -1);
	Aggregate highercard(engine().newVar(), setid, 1, AggType::CARD, AggSign::UB, AggSem::COMP, -1);
	internalAdd(highercard, engine());
	internalAdd(lowercard, engine());
	internalAdd(Disjunction({mkPosLit(highercard.head)}), engine());
	internalAdd(Disjunction({mkPosLit(lowercard.head)}), engine());

	for(uint i=0; i<equalities.size(); ++i){
		// if eq[i] => diseq[i]
		internalAdd(Disjunction({mkNegLit(equalities[i]), mkPosLit(disequalities[i])}), engine());
		if(i<equalities.size()-1){
			// if diseq[i] => diseq[i+1]
			internalAdd(Disjunction({mkNegLit(disequalities[i]), mkPosLit(disequalities[i+1])}), engine());
		}
		if(i>0){
			// if eq[i] => ~diseq[i-1]
			internalAdd(Disjunction({mkNegLit(equalities[i]), mkNegLit(disequalities[i-1])}), engine());
			// if ~diseq[i] => ~diseq[i-1]
			internalAdd(Disjunction({mkPosLit(disequalities[i]), mkNegLit(disequalities[i-1])}), engine());
		}
	}
}
