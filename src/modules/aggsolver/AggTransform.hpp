#ifndef AGGTRANSFORM_HPP_
#define AGGTRANSFORM_HPP_

#include <vector>

namespace MinisatID{

class PCSolver;
class AggSolver;

namespace Aggrs{

class TypedSet;
typedef std::vector<Aggrs::TypedSet*> vps;

/**
 * Checks whether the same literal occurs multiple times in the set
 * If this is the case, all identical literals are combined into one.
 *
 * @post: the literals are sorted according to weight again
 */

class AggTransform;
const std::vector<AggTransform*>& getTransformations();
//void doTransformations(AggSolver* solver, TypedSet* set, vps& sets, bool& unsat, bool& sat);

class AggTransform{
public:
	virtual void transform(AggSolver* solver, TypedSet* set, vps& sets, bool& unsat, bool& sat) const = 0;
};

class SetReduce : public AggTransform{
public:
	void transform(AggSolver* solver, TypedSet* set, vps& sets, bool& unsat, bool& sat) const;
};

class PartitionIntoTypes : public AggTransform{
public:
	void transform(AggSolver* solver, TypedSet* set, vps& sets, bool& unsat, bool& sat) const;
};

class AddTypes : public AggTransform{
public:
	void transform(AggSolver* solver, TypedSet* set, vps& sets, bool& unsat, bool& sat) const;
};

class MinToMax : public AggTransform{
public:
	void transform(AggSolver* solver, TypedSet* set, vps& sets, bool& unsat, bool& sat) const;
};

class MaxToSAT : public AggTransform{
public:
	void transform(AggSolver* solver, TypedSet* set, vps& sets, bool& unsat, bool& sat) const;
};

class VerifyWeights : public AggTransform{
public:
	void transform(AggSolver* solver, TypedSet* set, vps& sets, bool& unsat, bool& sat) const;
};

class AddHeadImplications : public AggTransform{
public:
	void transform(AggSolver* solver, TypedSet* set, vps& sets, bool& unsat, bool& sat) const;
};

class CardToEquiv : public AggTransform{
public:
	void transform(AggSolver* solver, TypedSet* set, vps& sets, bool& unsat, bool& sat) const;
};

class MapToSetOneToOneWithAgg : public AggTransform{
public:
	void transform(AggSolver* solver, TypedSet* set, vps& sets, bool& unsat, bool& sat) const;
};

class MapToSetOneToOneWithAggImpl : public AggTransform{
public:
	void transform(AggSolver* solver, TypedSet* set, vps& sets, bool& unsat, bool& sat) const;
};

bool transformSumsToCNF(vps& sets, MinisatID::PCSolver* pcsolver);

}
}

#endif /* AGGTRANSFORM_HPP_ */


//bool transformOneToOneSetToSignMapping(TypedSet* set, vps& sets);
