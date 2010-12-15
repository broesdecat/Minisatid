#ifndef AGGPRINT_HPP_
#define AGGPRINT_HPP_

namespace MinisatID {
namespace Aggrs{
class TypedSet;
class Agg;

void setAdded();
void aggrAdded();
void litPropagated();
void explanationGenerated();
void sets();

void print(int verbosity, const TypedSet&, bool endl = false);
void print(int verbosity, const Agg& c, bool endl = false);

}
}

#endif /* AGGPRINT_HPP_ */
