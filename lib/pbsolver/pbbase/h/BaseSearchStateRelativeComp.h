#ifndef BASESEARCHSTATERELATIVECOMP_H_
#define BASESEARCHSTATERELATIVECOMP_H_

#include <iostream>
#include <math.h>
#include <stdio.h>
#include "Global.h"

namespace MiniSatPP {
#define gamma  0.134380000001 // 0.129030517578
 
#define beta 0.350030517578// 0.100030517578 
#define alpa 0.30003051757812504//0.24003051757812507 
struct BaseSearchStateRelativeComp {
    BaseSearchStateRelativeComp* parent;
    int index;
	int lastRelevent;
	unsigned int baseMul;
	uint64 cnfSize;
	uint64 carryCost;
	uint64 hCnfSize;
	uint64 currentChain;
	uint64 carryins;
	BaseSearchStateRelativeComp(BaseSearchStateRelativeComp* parent_, int lastRelevent_ ,unsigned int baseMul_,
					uint64 cnfSize_, uint64 carryCost_,
					uint64 hCnfSize_,uint64 currentChain_,
					uint64 carryins_) :
					parent(parent_), index(0),lastRelevent(lastRelevent_) ,baseMul(baseMul_),
					cnfSize(cnfSize_),  carryCost(carryCost_),
					hCnfSize(hCnfSize_),currentChain(currentChain_),
					carryins(carryins_) {};
};

inline double ratio(uint64 x,uint64 y) {
	if (x==y)       return 0.5;
	else if (x < y) {
		if (y==0) printf("zero devsion");
		return 1 -((double )x/(2*y));
	}
    else  {
    	if (x==0) printf("zero devsion");
    	return ((double )y/(2*x));
    }
}
       
//returns true iff (a,b) is better then (c,d)
inline bool relComp(uint64 a,uint64 b, uint64 c, uint64 d) {
	//std::cout<<"relomp(" <<a<<", "<<b<<", "<<c<<", "<<d<<")="<<((1-gamma) * ratio(a,c) + gamma * ratio(b,d))<<"\n";
	return ((1-gamma) * ratio(a,c) + gamma * ratio(b,d)) > 0.5;
	//return (1-beta)*pow(a*ratio(b,a),alpa)+ (beta)*pow(b*ratio(a,b),alpa) < (1-beta)*pow(c*ratio(d,c),alpa)+ (beta)*pow(d*ratio(c,d),alpa);
	//return a<c;
}

}
#endif /*BASESEARCHSTATERELATIVECOMP_H_*/
