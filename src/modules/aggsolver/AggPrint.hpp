//LICENSEPLACEHOLDER
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

template<class T>
void NoSupportForBothSignInProductAgg(T& stream, const Lit& one, const Lit& two){
	stream <<"Product aggregates in which both the literal and its negation occur "
			"are currently not supported. Replace ";
	Print::print(stream, one);
	stream <<"or ";
	Print::print(stream, two);
	stream <<"by a tseitin.\n";
	stream.flush();
}

}
}

#endif /* AGGPRINT_HPP_ */
