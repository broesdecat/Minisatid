#include "solvers/modules/aggsolver/AggComb.hpp"

#include "solvers/modules/AggSolver.hpp"
#include "solvers/modules/aggsolver/FullyWatched.hpp"
#include "solvers/modules/aggsolver/PartiallyWatched.hpp"

#include "solvers/theorysolvers/PCSolver.hpp"

#include <algorithm>

#include <stdint.h>
#include <inttypes.h>
#include <limits.h>

using namespace std;
using namespace MinisatID;
using namespace Aggrs;

const WL& Watch::getWL() const {
	return getSet()->getWL()[index];
}

/**
 * Important: to justify a head, often several body literals have to become FALSE
 * For such literals, they have to be justified if they are NEGATIVE
 *
 * Also, if a literal has to become FALSE, its INVERSION should be added to the justification!
 */
bool Aggrs::oppositeIsJustified(const WL& l, vec<int>& currentjust, bool real, AggSolver const * const solver) {
	if (real) {
		return solver->value(l.getLit()) != l_True;
	} else {
		return solver->value(l.getLit()) != l_True && (!sign(l.getLit()) || isJustified(
																						var(l.getLit()),
																						currentjust));
	}
}

bool Aggrs::isJustified(const WL& l, vec<int>& currentjust, bool real, AggSolver const * const solver) {
	if (real) {
		return solver->value(l.getLit()) != l_False;
	} else {
		return solver->value(l.getLit()) != l_False && (sign(l.getLit()) || isJustified(
																						var(l.getLit()),
																						currentjust));
	}
}

bool Aggrs::isJustified(Var x, vec<int>& currentjust) {
	return currentjust[x] == 0;
}

///////
// DEBUG
///////

void Aggrs::printAgg(const TypedSet& c, bool endl) {
	report("%s{", c.getType()->getName());
	for (vwl::const_iterator i = c.getWL().begin(); i < c.getWL().end(); ++i) {
		report(" ");
		gprintLit((*i).getLit());
		lbool value = c.getSolver()->propagatedValue((*i).getLit());
		report("(%s)", value==l_Undef?"X":value==l_True?"T":"F");
		report("=%s", printWeight((*i).getWeight()).c_str());
	}
	if (endl) {
		report(" }\n");
	} else {
		report(" }");
	}
}

void Aggrs::printAgg(const Agg& ae, bool printendline) {
	gprintLit(ae.getHead());
	lbool value = ae.getSet()->getSolver()->propagatedValue(ae.getHead());
	report("(%s)", value==l_Undef?"X":value==l_True?"T":"F");
	TypedSet* set = ae.getSet();
	if (ae.isLower()) {
		report(" <- ");
	} else {
		report(" <- %s <= ", printWeight(ae.getBound()).c_str());
	}
	printAgg(*set, false);
	if (ae.isLower()) {
		//reportf(" <= %s. Known values: bestcertain=%s, bestpossible=%s\n", printWeight(ae.getLowerBound()).c_str(), printWeight(set->getCC()).c_str(), printWeight(set->getCP()).c_str());
		report(" <= %s, ", printWeight(ae.getBound()).c_str());
	} else {
		//reportf(". Known values: bestcertain=%s, bestpossible=%s\n", printWeight(set->getCC()).c_str(), printWeight(set->getCP()).c_str());
		report(", ");
	}
	report("ESV = %d.", ae.getSet()->getESV());
	if(printendline){
		report("\n");
	}
}
