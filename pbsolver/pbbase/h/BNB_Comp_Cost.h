#ifndef BNB_COMP_COST_H_  
#define BNB_COMP_COST_H_
namespace PBSolver{
/**
	 * @pre 
	 * 			 	for all i ws[i][0]>ws[i+1][0] and ws[i][0]>0 ws[i][1]>0 
	 * @param ws:  
	 * 				ws[i][0] = weight i
	 *  			ws[i][1] = number of weight i in constraint
	 * @return	SearchMetaData*  
*/
SearchMetaData* bnb_Comp_Cost_search(unsigned int weights[][2],int length,std::vector<unsigned int>& primes,unsigned int cutoff,bool nonPrimePossible,bool abstraction);
}

#endif /*BNB_COMP_COST_H_*/
