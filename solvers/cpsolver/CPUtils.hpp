#ifndef CPUTILS_H
#define CPUTILS_H

#include <gecode/kernel.hh>
#include <gecode/driver.hh>
#include <gecode/int.hh>
#include <gecode/minimodel.hh>

#include <solvers/utils/Utils.hpp>

namespace CP {
	bool isTrue(Gecode::BoolVar var);
	bool isFalse(Gecode::BoolVar var);
	bool isAssigned(Gecode::BoolVar var);

	Gecode::IntRelType negate(Gecode::IntRelType eq);

	Gecode::IntRelType toRelType(MINISAT::EqType eq);
}

#endif /*CPUTILS_H*/
