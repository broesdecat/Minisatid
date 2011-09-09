#ifndef PB2CNF_HPP_
#define PB2CNF_HPP_

#include <vector>

namespace MiniSatPP {

class Lit;
namespace MiniSat{
	class Clause;
}
template<class T>class vec;

void toCNF(std::vector<std::vector<Lit> >& cnf, const vec<MiniSat::Clause*>& clauses, const vec<int>& assigns, const vec<int>& level);

}
#endif /* PB2CNF_HPP_ */
