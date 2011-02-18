//LICENSEPLACEHOLDER
#ifndef SOLVERI_H_
#define SOLVERI_H_

#include <cstdio>

#include "utils/Utils.hpp"

namespace MinisatID {

class Solution;
class WLSImpl;

class LogicSolver{
private:
	SolverOption _modes;
	MinisatID::WLSImpl* _parent;
public:
	LogicSolver(MinisatID::SolverOption modes, MinisatID::WLSImpl* inter)
			:_modes(modes), _parent(inter){};
	virtual ~LogicSolver(){};

	virtual bool 	simplify() = 0;
	virtual void 	finishParsing	(bool& present, bool& unsat) = 0;

	virtual bool	solve(const vec<Lit>& assumptions, Solution* sol) = 0;

			int 	verbosity		() const	{ return modes().verbosity; }
	const SolverOption& modes		() const	{ return _modes; }

	MinisatID::WLSImpl* getParent	() const { return _parent; }

	virtual void 	printStatistics	() const = 0;
};

}

#endif /* SOLVERI_H_ */
