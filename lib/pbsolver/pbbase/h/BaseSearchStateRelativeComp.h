#ifndef BASESEARCHSTATERELATIVECOMP_H_
#define BASESEARCHSTATERELATIVECOMP_H_

#include <iostream>
#include <math.h>
#include <stdio.h>

namespace MiniSatPP {
#define gamma  0.134380000001 // 0.129030517578
 
#define beta 0.350030517578// 0.100030517578 
#define alpa 0.30003051757812504//0.24003051757812507 
struct BaseSearchStateRelativeComp {
    BaseSearchStateRelativeComp* parent;
    int index;
	int lastRelevent;
	unsigned int baseMul;
	unsigned long long cnfSize;
	unsigned long long carryCost;
	unsigned long long hCnfSize;
	unsigned long long currentChain;
	unsigned long long carryins;
	BaseSearchStateRelativeComp(BaseSearchStateRelativeComp* parent_, int lastRelevent_ ,unsigned int baseMul_,
					unsigned long long cnfSize_, unsigned long long carryCost_,
					unsigned long long hCnfSize_,unsigned long long currentChain_,
					unsigned long long carryins_) : 
					parent(parent_), index(0),lastRelevent(lastRelevent_) ,baseMul(baseMul_),
					cnfSize(cnfSize_),  carryCost(carryCost_),
					hCnfSize(hCnfSize_),currentChain(currentChain_),
					carryins(carryins_) {};
};

inline double ratio(unsigned long long x,unsigned long long y) {
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
inline bool relComp(unsigned long long a,unsigned long long b, unsigned long long c, unsigned long long d) {
	//std::cout<<"relomp(" <<a<<", "<<b<<", "<<c<<", "<<d<<")="<<((1-gamma) * ratio(a,c) + gamma * ratio(b,d))<<"\n";
	return ((1-gamma) * ratio(a,c) + gamma * ratio(b,d)) > 0.5;
	//return (1-beta)*pow(a*ratio(b,a),alpa)+ (beta)*pow(b*ratio(a,b),alpa) < (1-beta)*pow(c*ratio(d,c),alpa)+ (beta)*pow(d*ratio(c,d),alpa);
	//return a<c;
}

}
#endif /*BASESEARCHSTATERELATIVECOMP_H_*/
