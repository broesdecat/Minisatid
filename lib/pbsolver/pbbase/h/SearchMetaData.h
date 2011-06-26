#ifndef SEARCHMETADATA_H_
#define SEARCHMETADATA_H_

#include <sys/time.h>
#include <time.h>
#include <vector>
#include <string>

#include "Global.h"

namespace MiniSatPP {
class SearchMetaData {
	
  public:
  	std::vector<int> base;
  	std::vector<uint64> carry;
  	std::vector<uint64> inputs;
  	uint64 emptyBaseNOI;
	uint64 cost;
	uint64 inputCountCost;
	uint64 carryOnlyCost;
	uint64 compCost;
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
	void finalize(uint64 cost);
	virtual ~SearchMetaData();
	void print();
	
  private: 
  	struct timeval startVal;
};       

}

#endif /*SEARCHMETADATA_H_*/
