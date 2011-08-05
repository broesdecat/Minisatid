#ifndef BINCONSTR_HPP
#define BINCONSTR_HPP
#include "modules/IntVar.hpp"

namespace MinisatID{

class BinaryConstraint: public Propagator{
	IntVar* left, right;
	EqType t;
};

}

#endif //BINCONSTR_HPP
