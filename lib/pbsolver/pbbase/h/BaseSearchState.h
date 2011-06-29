#ifndef BASESEARCHSTATE_H_
#define BASESEARCHSTATE_H_

#include "Global.h"

namespace MiniSatPP {
struct BaseSearchState {
    BaseSearchState* parent;
    int index;
	int lastRelevent;
	unsigned int baseMul;
	uint64 cost;
	uint64 hCost;
	uint64 carryins;
	BaseSearchState(BaseSearchState* parent_, int lastRelevent_ ,unsigned int baseMul_,
					unsigned long cost_,unsigned long hCost_,
					unsigned long carryins_) : 
					parent(parent_), index(0),lastRelevent(lastRelevent_) ,baseMul(baseMul_),
					cost(cost_),hCost(hCost_),
					carryins(carryins_) {};
};
}
       
#endif /*BASESEARCHSTATE_H_*/
