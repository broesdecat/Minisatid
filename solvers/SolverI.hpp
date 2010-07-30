#ifndef SOLVERI_H_
#define SOLVERI_H_

#include <cstdio>
using namespace std;

#include "solvers/utils/Solverfwd.hpp"

class Data{
private:
	ECNF_mode _modes;
public:
	Data(ECNF_mode modes):_modes(modes){};
	virtual ~Data(){};

	virtual void 	setNbModels(int nb) = 0;

	virtual bool 	simplify() = 0;
	virtual bool 	solve() = 0;
	virtual bool 	finishParsing() = 0;

	int 			verbosity() const	{ return modes().verbosity; }
	const ECNF_mode& modes()	const	{ return _modes; }
};

#endif /* SOLVERI_H_ */
