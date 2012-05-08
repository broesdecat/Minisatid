#include <cstdio>
#include <vector>
#include "../h/SearchMetaData.h"
#include "../h/GenralBaseFunctions.h"
#include "../h/ForwardSearch.h"

namespace MiniSatPP {
	
#define length(a) ( sizeof ( a ) / sizeof ( *a ) )

struct sData{
       long unsigned int lastRelevent;
       unsigned long cost;  
       long unsigned int carryIns;
       unsigned int baseMul;
};
   
static unsigned long findOpt(unsigned int wights[][2],struct sData data,std::vector<int> &lastBase,SearchMetaData &md,unsigned long minNumOfBits,unsigned int sum[],std::vector<unsigned int>& primes);

/**
	 * @pre 
	 * 			 	for all i ws[i][0]>ws[i+1][0] and ws[i][0]>0 ws[i][1]>0 
	 * @param ws:  
	 * 				ws[i][0] = weight i
	 *  			ws[i][1] = number of weight i in constraint
	 * @return	SearchMetaData*  
*/
SearchMetaData* findBaseFWD(unsigned int weights[][2],int length,std::vector<unsigned int>& primes,unsigned int cutoff){
		SearchMetaData*  md = new SearchMetaData(lg2(weights[0][0]),cutoff,weights[0][0],length,"DFS_cost_carry"); //preperations
		unsigned int sum[length+1];
		sum[0] = 0;
		for(int i=0;i<length;i++)
			sum[i+1]=sum[i]+weights[i][1];
		struct sData data={(long unsigned int)length,0,0,1};
		std::vector<int> tempBase;
		md->basesEvaluated++;
		md->finalize(findOpt(weights,data,tempBase,(*md),inputCountEval(weights, md->base,length),sum,primes)); 
		return md;
}
	
	static unsigned long findOpt(unsigned int wights[][2],struct sData data,std::vector<int> &lastBase,
						       SearchMetaData &md, unsigned long minNumOfBits,unsigned int sum[],std::vector<unsigned int>& primes){
			md.nodesExpended++;
			register unsigned int  bm =  data.baseMul;
			for(unsigned int i=0;i<primes.size() && bm*primes[i]<=wights[0][0];i++){	
				md.basesEvaluated++;
				register unsigned int p = primes[i];
				register unsigned long newCost = data.carryIns;
				register unsigned long newLastRelevent = 0;
				register unsigned long cutC = 0; 
				register unsigned long newCarryIns = 0; 
				for(unsigned long j=0;j<data.lastRelevent;j++) {
					register unsigned int temp = wights[j][0] /bm;
					if (temp==0) goto l1;
					newCost+=(temp % p)*wights[j][1];
					switch(temp>=p) {
						case 0: break;
						default: switch(temp>=2*p) {
									case 0: newCarryIns+=wights[j][1];  break; 
									default: newLastRelevent++; cutC+=(temp/p)*wights[j][1];
								}
					}
				}
			l1: newCarryIns += newCost / p; 
				newCost+=data.cost;		
				switch( newLastRelevent ) {
					    case 0 : 
							newCost  +=  newCarryIns;
							if (newCost<minNumOfBits) { 
								md.base.assign(lastBase.begin(),lastBase.end()); 
								md.base.push_back(p);
								minNumOfBits = newCost;
							}
						break;
					    default: cutC+= newCarryIns +  newCost;
					    		if (cutC<minNumOfBits) {
					    			md.base.assign(lastBase.begin(),lastBase.end()); 
									md.base.push_back(p);
									minNumOfBits = cutC;
					    		} 
					    		if (newCost+sum[newLastRelevent]+newCarryIns<minNumOfBits) {
									struct sData newData={newLastRelevent,newCost,newCarryIns,bm*p};			
									lastBase.push_back(p);
									minNumOfBits = std::min(minNumOfBits, findOpt(wights,newData,lastBase,md,minNumOfBits,sum,primes));
									lastBase.pop_back();
								 }
				}	
			}
			return minNumOfBits;
	}



int mainFWD(int argc, char **argv) {
	unsigned int ws[][2] = {{1000000,100},{777777,100},{640487,100},{47360,100},{10127,100},
			{9873,100},{8153,100},{7543,100},{6937,100},{5342,100},{4283,100},
				{3761,100},{2344,100},{231,100},{123,12}};
	PrimesLoader pl("P1.TXT");
    unsigned int cufOff = pl.loadPrimes(ws[0][0],1000000);				
	SearchMetaData* md = findBaseFWD(ws,length(ws),pl.primeVector(),cufOff);
	md->print();
	delete md;
	return 0; 
}
}
