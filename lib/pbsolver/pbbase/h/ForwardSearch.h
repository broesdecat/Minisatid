#ifndef FORWARDSEARCH_H_
#define FORWARDSEARCH_H_

namespace MiniSatPP {
/**
 * @pre 
 * 			 	for all i ws[i][0]>ws[i+1][0] and ws[i][0]>0 ws[i][1]>0 
 * @param ws:  
 * 				ws[i][0] = weight i
 *  			ws[i][1] = number of weight i in constraint
 * @return	SearchMetaData*  
 */
SearchMetaData* findBaseFWD(unsigned int weights[][2],int length,std::vector<unsigned int>& primes,unsigned int cutoff);
}


#endif /*FORWARDSEARCH_H_*/
