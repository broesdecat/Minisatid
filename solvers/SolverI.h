#ifndef SOLVERI_H_
#define SOLVERI_H_

#include <stdio.h>
using namespace std;

class Data{
public:
	Data(){};
	virtual ~Data(){};

	virtual void setNbModels(int nb) = 0;
	virtual void setRes(FILE* f) = 0;

	virtual bool 	simplify() = 0;
	virtual bool 	solve() = 0;
	virtual void 	finishParsing() = 0;
};

#endif /* SOLVERI_H_ */
