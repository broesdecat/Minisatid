#ifndef AGGPRINT_HPP_
#define AGGPRINT_HPP_

namespace MinisatID {
namespace Aggrs{
class TypedSet;
class Agg;

void print(const TypedSet&, bool endl = false);
void print(const Agg& c, bool endl = false);

}
}

#endif /* AGGPRINT_HPP_ */
