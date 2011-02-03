#ifndef RELATIVEBASESEARCH_H
#define RELATIVEBASESEARCH_H

namespace MiniSatPP {
/**
	 * @pre 
	 * 			 	for all i ws[i][0]>ws[i+1][0] and ws[i][0]>0 ws[i][1]>0 
	 * @param ws:  
	 * 				ws[i][0] = weight i
	 *  			ws[i][1] = number of weight i in constraint
	 * @return	SearchMetaData*  
*/
SearchMetaData* bnb_Relative_search(unsigned int weights[][2],int length,std::vector<unsigned int>& primes,unsigned int cutoff,bool primesOnly,bool abstraction);
}


#endif /*RELATIVEBASESEARCH_H*/
