#include <cstdio>
#include <vector>
#include <map>
#include "../h/SearchMetaData.h"
#include "../h/THeap.h"
#include "../h/BaseSearchState.h"
#include "../h/GenralBaseFunctions.h"
#include "../h/BNB_SOD_Carry_Cost.h"

namespace MiniSatPP {
	
#define length(a) ( sizeof ( a ) / sizeof ( *a ) )

static inline void createChild(struct BaseSearchState* father,register unsigned int msb,register unsigned int wights[][2],unsigned int sum[],uint64* bestFound,
							   struct BaseSearchState** bestStateFound,THeap& que,SearchMetaData& md,std::vector<bss>& old,std::map<unsigned int,bss>& homomorphism,bool abstraction,bool sumOfDig);

/**
	 * @pre 
	 * 			 	for all i ws[i][0]>ws[i+1][0] and ws[i][0]>0 ws[i][1]>0 
	 * @param ws:  
	 * 				ws[i][0] = weight i
	 *  			ws[i][1] = number of weight i in constraint
	 * @return	SearchMetaData*  
*/
SearchMetaData* bnb_SOD_Carry_Cost_search(unsigned int weights[][2],int length,std::vector<unsigned int>& primes,unsigned int cutoff,bool nonPrimePossible,bool abstraction,bool sumOfDig){
		SearchMetaData*  md = NULL;  //preperations
		/*if (sumOfDig) md =  new SearchMetaData(lg2(weights[0][0]),cutoff,weights[0][0],length,"BNB_cost_sumOfDigits");
		else 		  md =  new SearchMetaData(lg2(weights[0][0]),cutoff,weights[0][0],length,"BNB_cost_carry"); 
		THeap que;
		std::map<unsigned int,bss> homomorphism;
		unsigned int sum[length+1];
		sum[0] = 0;
		uint64 temp=0;
		for(int i=0;i<length;i++) {
			sum[i+1]=sum[i]+weights[i][1];	
			temp+=weights[i][0]*weights[i][1];
		}
		BaseSearchState* startState=new BaseSearchState(0,length,1,0,0,0);
		BaseSearchState* bestStateFound(0);
		que.offer(startState);
		uint64 bestFound = inputCountEval(weights, md->base,length);
		if (bestFound>temp) { // relaxs betwin The empty base and the Binary base
			bestFound =temp;
			bestStateFound = startState;
		}
		std::vector<bss> old;
		while(!que.isEmpty() && que.peek()->hCost < bestFound ) { //main A star loop;
			md->nodesExpended++;
			struct BaseSearchState* father = que.poll();
			old.push_back(father);
			for(unsigned int i=0;i<primes.size() &&  father->baseMul*primes[i]<=weights[0][0];i++){
				createChild(father,primes[i],weights,sum,&bestFound,&bestStateFound,que,*md,old,homomorphism,abstraction,sumOfDig); //create regular chiled
				if (nonPrimePossible && father->parent!=0 )  //search for non primes
					createChild(father->parent,(father->baseMul / father->parent->baseMul)*primes[i],weights,sum,&bestFound,&bestStateFound,que,*md,old,homomorphism,abstraction,sumOfDig);
			}
		}
		if (bestStateFound!=0) {
			std::vector<int> &base =  md->base;
			base.clear(); 
			BaseSearchState* temp = bestStateFound;
			while (temp->parent!=0){
				base.insert(base.begin(),temp->baseMul / temp->parent->baseMul);
				temp = temp->parent;
			} 
		}
		md->finalize(bestFound);
		for(unsigned int i=0;i<old.size();i++)
			delete old[i];*/
		return md;
}



static inline void createChild(struct BaseSearchState* father,register unsigned int msb,register unsigned int wights[][2],unsigned int sum[],uint64* bestFound,
					           struct BaseSearchState** bestStateFound,THeap& que,SearchMetaData& md,std::vector<bss>& old,std::map<unsigned int,bss>& homomorphism,bool abstraction,bool sumOfDig) {
	md.basesEvaluated++;
	register uint64 childCost = father->carryins;
	register uint64 childCarryins = 0;
	register uint64 childCutCost = 0;
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
l1: switch(childLastRelevent) {
		case 0 :
				if (!sumOfDig) childCost+=childCost/msb; 
				childCost+= father->cost + childCarryins;
				if (childCost<*bestFound){
					bss child = new BaseSearchState(father,0,bm*msb,childCost,childCost,0); 
					old.push_back(child);
					(*bestFound) = childCost;
					(*bestStateFound) = child;
				}
				return;
		default:
				if (!sumOfDig) childCarryins+=childCost / msb;
				childCost += father->cost;
				register uint64 h = sum[childLastRelevent]+childCarryins+childCost;
				if (h>=*bestFound) return;
				childCutCost+=childCarryins+childCost;
				bss temp;
				if (!abstraction){
					temp = new BaseSearchState(father,childLastRelevent,bm*msb,childCost,h,childCarryins);
					que.offer(temp); 
					md.insertedToQue++;
				}
				else {
					temp = homomorphism[bm*msb];
					if (temp) {
					     if (childCost+childCarryins < temp->cost+temp->carryins){
					     	temp->parent = father;
					    	temp->cost  = childCost;
					    	temp->hCost = h; 
							temp->carryins = childCarryins;
					     	que.update(temp);
					     }  
					}
					else {
						 temp = new BaseSearchState(father,childLastRelevent,bm*msb,childCost,h,childCarryins);
						 homomorphism[bm*msb] = temp;
						 que.offer(temp); 
						 md.insertedToQue++;
					}
				}
				if (childCutCost<*bestFound) {
					(*bestFound) = childCutCost;
					(*bestStateFound) = temp;
				}
	}
}
	
int mainBNB_SOD_Carry_Cost_search(int argc, char **argv) {
	unsigned int ws[][2] = {{1000000,100},{777777,100},{640487,100},{47360,100},{10127,100},
			{9873,100},{8153,100},{7543,100},{6937,100},{5342,100},{4283,100},
				{3761,100},{2344,100},{231,100},{123,12}};
	std::vector<unsigned int> pri;
  	loadPrimes("P1.TXT",pri,ws[0][0],1000000);
	SearchMetaData* md = bnb_SOD_Carry_Cost_search(ws,length(ws),pri,1000000,false,true,false);
	md->print();
	delete md;
	return 0;  
}

}
