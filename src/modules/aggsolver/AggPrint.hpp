#ifndef AGGPRINT_HPP_
#define AGGPRINT_HPP_

#include <vector>
#include "utils/Print.hpp"

namespace MinisatID {
class AggSolver;

namespace Aggrs{
class TypedSet;
class Agg;
class Watch;

void setAdded();
void aggrAdded();
void litPropagated();
void explanationGenerated();
void sets();

void printWatches(int verbosity, AggSolver const * const solver, const std::vector<std::vector<Watch*> >& tempwatches);

void print(int verbosity, const TypedSet&, bool endl = false);
void print(int verbosity, const Agg& c, bool endl = false);

}
}

#endif /* AGGPRINT_HPP_ */
