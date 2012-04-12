#include "../h/SearchMetaData.h"
#include <iostream>
#include <math.h>

namespace MiniSatPP {
	
SearchMetaData::SearchMetaData(int size,unsigned int primesCutOf_,unsigned int mxcoff,int len,std::string algt) :
		 base(size,2),carry(size,0),inputs(size,0),emptyBaseNOI(0),cost(0),inputCountCost(0),carryOnlyCost(0),compCost(0),basesEvaluated(0),runTime(0),
		 insertedToQue(0),nodesExpended(0),fEnvSize(0),primesCutOf(primesCutOf_), 
		 maxCoffes(mxcoff),numOfCoffes(0),numOfDifCoffes(len),algType(algt) {
  gettimeofday(&startVal, NULL);  
  while (pow(2,base.size())>mxcoff) {
  		base.pop_back();
  }
}  
 

SearchMetaData::~SearchMetaData() {}

void SearchMetaData::finalize(unsigned long long cost_) {
  struct timeval endVal;
  gettimeofday(&endVal, NULL); 
  cost = cost_;
  runTime =   (endVal.tv_sec - startVal.tv_sec)*1000000 + endVal.tv_usec - startVal.tv_usec;
}

void SearchMetaData::print() {
	std::cout<<algType<<" ,cost= "<<cost<<" ,basesEvaluated= "<<basesEvaluated
			<<" ,Runtime= "<<runTime<<" ,InsertedToQue= "<<insertedToQue<<
			" ,nodesExpended= "<<nodesExpended<<" ,primesCutOf= "<<primesCutOf<<"\n";
}


 
}