#ifndef AGGTRANSFORM_HPP_
#define AGGTRANSFORM_HPP_

#include <vector>

namespace MinisatID{

class PCSolver;

namespace Aggrs{

class TypedSet;
typedef std::vector<Aggrs::TypedSet*> vps;

/**
 * Checks whether the same literal occurs multiple times in the set
 * If this is the case, all identical literals are combined into one.
 *
 * @post: the literals are sorted according to weight again
 */
bool transformSetReduction(TypedSet* set, vps& sets);
bool transformTypePartition(TypedSet* set, vps& sets);
bool transformAddTypes(TypedSet* set, vps& sets);
bool transformMinToMax(TypedSet* set, vps& sets);
bool transformMaxToSAT(TypedSet* set, vps& sets);
bool transformSplitAggregate(TypedSet* set, vps& sets);
bool transformVerifyWeights(TypedSet* set, vps& sets);
bool transformOneToOneSetToAggMapping(TypedSet* set, vps& sets);
bool transformCardGeqOneToEquiv(TypedSet* set, vps& sets);

bool transformSumsToCNF(vps& sets, MinisatID::PCSolver* pcsolver);

}
}

#endif /* AGGTRANSFORM_HPP_ */


//bool transformOneToOneSetToSignMapping(TypedSet* set, vps& sets);
