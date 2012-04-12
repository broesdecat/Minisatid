#include <cstdio>
#include <vector>
#include <map>
#include <iostream>
#include "../h/SearchMetaData.h"
#include "../h/THeapComp.h"
#include "../h/BaseSearchStateRelativeComp.h"
#include "../h/GenralBaseFunctions.h"
#include "../h/RelativeBaseSearch.h"

namespace MiniSatPP {
	
#define length(a) ( sizeof ( a ) / sizeof ( *a ) )
#define betterThenBest(a,b) relComp(a->hCnfSize,a->carryCost,b->cnfSize,b->carryCost)

static inline void createChild(bssr father,register unsigned int msb,register unsigned int wights[][2],unsigned int sum[],unsigned long long& cnfSizeOfBestFound,unsigned long long& carryOfBestFound,  
							   bssr* bestStateFound,THeapComp& que,SearchMetaData& md,std::vector<bssr>& old,std::map<unsigned int,bssr>& homomorphism,bool abstraction);

static inline unsigned long long calcCarryCost(std::vector<unsigned long long> &carry) {
	unsigned long long cuerntChainLegth = 0;
	unsigned long long carryCost = 0;
	for(unsigned int i=0;i<carry.size();i++){
		if (carry[i] == 0)
			cuerntChainLegth = 0;
		else {
			cuerntChainLegth++;
			carryCost+=carry[i]*cuerntChainLegth*cuerntChainLegth;
		}
	}
	return 	carryCost;
}


/**
	 * @pre 
	 * 			 	for all i ws[i][0]>ws[i+1][0] and ws[i][0]>0 ws[i][1]>0 
	 * @param ws:  
	 * 				ws[i][0] = weight i
	 *  			ws[i][1] = number of weight i in constraint
	 * @return	SearchMetaData*  
*/ 
SearchMetaData* bnb_Relative_search(unsigned int weights[][2],int length,std::vector<unsigned int>& primes,unsigned int cutoff,bool nonPrimePossible,bool abstraction){
		SearchMetaData*  md = new SearchMetaData(lg2(weights[0][0]),cutoff,weights[0][0],length,"BNB_relative_comp"); //preperations
		THeapComp que;
		unsigned long long carryOfBestFound,cnfSizeOfBestFound;
		std::map<unsigned int,bssr> homomorphism;
		unsigned int sum[length+1];
		sum[0] = 0;
		unsigned long long temp=0;
		for(int i=0;i<length;i++) {
			sum[i+1]=sum[i]+weights[i][1];	
			temp+=weights[i][0]*weights[i][1];
		}
		temp = nlg2n2(temp);	
		bssr startState= new BaseSearchStateRelativeComp(0,length,1,0,0,0,0,0);
		bssr bestStateFound(0);
		que.offer(startState);
		std::vector<unsigned long long> carry;
		carryVecEval(weights, md->base,length,carry);
		carryOfBestFound = calcCarryCost(carry);
		//std::cout<<"empty base: cnfSize="<<temp<<", carryCost="<<0<<"\n";
		//for(unsigned int tt=0;tt<carry.size();tt++){
//			std::cout<<","<<carry[tt];
	//	}
		//std::cout<<"\n";
		cnfSizeOfBestFound = compCountEval(weights, md->base,length);
		//std::cout<<"binary base: length="<<md->base.size()<<" , cnfSize="<<cnfSizeOfBestFound<<", carryCost="<<carryOfBestFound<<"\n";
		if /*(true){*/(relComp(temp,0,cnfSizeOfBestFound,carryOfBestFound)) { // relaxs betwin The empty base and the Binary base
			bestStateFound = startState; 
			cnfSizeOfBestFound = temp;
			carryOfBestFound = 0;
		}
		std::vector<bssr> old;
		while(!que.isEmpty() &&  
		relComp(que.peek()->hCnfSize,que.peek()->carryCost,cnfSizeOfBestFound,carryOfBestFound)) {//main A star loop;
			md->nodesExpended++;
			bssr father = que.poll();
			old.push_back(father);
			for(unsigned int i=0;i<primes.size() &&  father->baseMul*primes[i]<=weights[0][0];i++){
				createChild(father,primes[i],weights,sum,cnfSizeOfBestFound,carryOfBestFound,&bestStateFound,que,*md,old,homomorphism,abstraction); //create regular chiled
				if (nonPrimePossible && father->parent!=0) { //create compresion chiled 
					createChild(father->parent,(father->baseMul / father->parent->baseMul)*primes[i],weights,sum,cnfSizeOfBestFound,carryOfBestFound,&bestStateFound,que,*md,old,homomorphism,abstraction);
				}
			}
		}
		if (bestStateFound!=0) {
			std::vector<int> &base =  md->base;
			base.clear(); 
			bssr temp = bestStateFound;
			while (temp->parent!=0){
				base.insert(base.begin(),temp->baseMul / temp->parent->baseMul);
				temp = temp->parent;
			} 
		}
		md->finalize(cnfSizeOfBestFound);
		for(unsigned int i=0;i<old.size();i++)
			delete old[i];
		//carry.clear();
		//carryVecEval(weights, md->base,length,carry);
		//unsigned long long byFunc = calcCarryCost(carry);
		//for(unsigned int tt=0;tt<carry.size();tt++){
	//		std::cout<<","<<carry[tt];
	//	}
		//std::cout<<"\n";
		//std::cout<<"best base data: cnfSize="<<cnfSizeOfBestFound<<", carryCost="<<carryOfBestFound<<" ,byFunc="<<byFunc<<"\n";
		return md;
}



static inline void createChild(bssr father,register unsigned int msb,register unsigned int wights[][2],unsigned int sum[],unsigned long long& cnfSizeOfBestFound,unsigned long long& carryOfBestFound,
					           bssr* bestStateFound,THeapComp& que,SearchMetaData& md,std::vector<bssr>& old,std::map<unsigned int,bssr>& homomorphism,bool abstraction) {
	md.basesEvaluated++;
	register unsigned long long childCost = father->carryins; 
	register unsigned long long childCarryins = 0; 
	register unsigned long long childCutCost = 0; 
	register int childLastRelevent = 0; 
	register unsigned int bm = father->baseMul;
	for(int i=0;i<father->lastRelevent;i++) {
		register unsigned int temp = wights[i][0] / bm;
		if (temp==0) goto l1;
		childCost+=(temp % msb)*wights[i][1];
		switch(temp>=msb) {
			case 0: break;
			default: switch(temp>=2*msb) {
						case 0: childCarryins+=wights[i][1]; break;
						default: childLastRelevent++; childCutCost +=(temp/msb)*wights[i][1];
					 }
		}
	}
l1:	unsigned long long ttt = childCost/msb;
 	childCarryins += ttt;
	int curC;
	unsigned long long cc = father->carryCost;
	if (ttt==0)
		curC = 0;
	else 
		curC = father->currentChain+1;
		cc  += curC * curC * ttt;
	switch(childLastRelevent) {
		case 0 :  
				childCost=nlg2n2(childCost)+father->cnfSize+nlg2n2(childCarryins);
				if (relComp(childCost,cc,cnfSizeOfBestFound,carryOfBestFound)){
					bssr child = new BaseSearchStateRelativeComp(father,0,bm*msb,childCost,cc,childCost,curC,0); 
					old.push_back(child);
					(*bestStateFound) = child;
					cnfSizeOfBestFound= childCost;
					carryOfBestFound  = cc;
				}
				return;
		default: 
				childCost = nlg2n2(childCost)+father->cnfSize;
				register unsigned long long h = nlg2n2(childCarryins)+childCost+sum[childLastRelevent];
				if (!relComp(h,cc,cnfSizeOfBestFound,carryOfBestFound)) return;     //(h>=*bestFound) return;
				childCutCost = nlg2n2(childCutCost + childCarryins)+childCost;
				bssr temp;
				if (!abstraction){
					temp = new BaseSearchStateRelativeComp(father,childLastRelevent,bm*msb,childCost,cc,h,curC,childCarryins);
					que.offer(temp); 
					md.insertedToQue++;
				}
				else {
				 	temp= homomorphism[bm*msb];
					if (temp) {
					     if (relComp(childCost+nlg2n2(childCarryins),cc,temp->cnfSize+nlg2n2(temp->carryins),temp->carryCost)) {  
					     	temp->parent = father;
					     	temp->cnfSize  = childCost;
					     	temp->hCnfSize = h; 
					     	temp->carryins = childCarryins;
					     	temp->carryCost = cc; 
					     	temp->currentChain = curC;
					     	que.update(temp);
					     }  
					}
					else {
						 temp = new BaseSearchStateRelativeComp(father,childLastRelevent,bm*msb,childCost,cc,h,curC,childCarryins);
						 homomorphism[bm*msb] = temp;
						 que.offer(temp); 
						 md.insertedToQue++;
					}
				}
				if (relComp(childCutCost,cc,cnfSizeOfBestFound,carryOfBestFound)) { 
					(*bestStateFound) = temp;
					cnfSizeOfBestFound=childCutCost;
					carryOfBestFound= cc;
				}
	}
}
	
int mainRel(int argc, char **argv) {
	unsigned int ws[][2] = {{1000000,100},{777777,100},{640487,100},{47360,100},{10127,100},
			{9873,100},{8153,100},{7543,100},{6937,100},{5342,100},{4283,100},
				{3761,100},{2344,100},{231,100},{123,12}};
	
  	PrimesLoader pl("P1.TXT");
    unsigned int cufOff = pl.loadPrimes(ws[0][0],1000000);				
	SearchMetaData* md = bnb_Relative_search(ws,length(ws),pl.primeVector(),cufOff,false,true);
	md->print();
	delete md;
	return 0;  
}
}