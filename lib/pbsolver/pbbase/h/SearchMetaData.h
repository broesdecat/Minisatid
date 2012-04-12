#ifndef SEARCHMETADATA_H_
#define SEARCHMETADATA_H_

#include <sys/time.h>
#include <time.h>
#include <vector>
#include <string>

namespace MiniSatPP {
class SearchMetaData {
	
  public:
  	std::vector<int> base;
  	std::vector<unsigned long long> carry;
  	std::vector<unsigned long long> inputs;
  	unsigned long long emptyBaseNOI;
	unsigned long long cost;
	unsigned long long inputCountCost;
	unsigned long long carryOnlyCost;
	unsigned long long compCost;
	unsigned long basesEvaluated;
	unsigned long runTime; //run time in micro secounds
	unsigned long insertedToQue;
	unsigned long nodesExpended; //==nodes extracted from que
	unsigned int fEnvSize;
	unsigned int primesCutOf;
	unsigned int maxCoffes;
	int numOfCoffes;
	int numOfDifCoffes;
	std::string algType;
	
	SearchMetaData(int size,unsigned int primesCutOf_,unsigned int mxcoff,int len,std::string algt);
	void finalize(unsigned long long cost);
	virtual ~SearchMetaData();
	void print();
	
  private: 
  	struct timeval startVal;
};       

}

#endif /*SEARCHMETADATA_H_*/
