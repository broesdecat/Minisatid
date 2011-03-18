/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
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

class AggTransformation;
const std::vector<AggTransformation*>& getTransformations();
//void doTransformations(AggSolver* solver, TypedSet* set, vps& sets, bool& unsat, bool& sat);

class AggTransformation{
public:
	virtual void transform(AggSolver* solver, TypedSet* set, vps& sets, bool& unsat, bool& sat) const = 0;
};

class SetReduce : public AggTransformation{
public:
	void transform(AggSolver* solver, TypedSet* set, vps& sets, bool& unsat, bool& sat) const;
};

class PartitionIntoTypes : public AggTransformation{
public:
	void transform(AggSolver* solver, TypedSet* set, vps& sets, bool& unsat, bool& sat) const;
};

class AddTypes : public AggTransformation{
public:
	void transform(AggSolver* solver, TypedSet* set, vps& sets, bool& unsat, bool& sat) const;
};

class MinToMax : public AggTransformation{
public:
	void transform(AggSolver* solver, TypedSet* set, vps& sets, bool& unsat, bool& sat) const;
};

class MaxToSAT : public AggTransformation{
public:
	void transform(AggSolver* solver, TypedSet* set, vps& sets, bool& unsat, bool& sat) const;
};

class VerifyWeights : public AggTransformation{
public:
	void transform(AggSolver* solver, TypedSet* set, vps& sets, bool& unsat, bool& sat) const;
};

class AddHeadImplications : public AggTransformation{
public:
	void transform(AggSolver* solver, TypedSet* set, vps& sets, bool& unsat, bool& sat) const;
};

class CardToEquiv : public AggTransformation{
public:
	void transform(AggSolver* solver, TypedSet* set, vps& sets, bool& unsat, bool& sat) const;
};

class MapToSetOneToOneWithAgg : public AggTransformation{
public:
	void transform(AggSolver* solver, TypedSet* set, vps& sets, bool& unsat, bool& sat) const;
};

class MapToSetWithSameAggSign : public AggTransformation{
public:
	void transform(AggSolver* solver, TypedSet* set, vps& sets, bool& unsat, bool& sat) const;
};

bool transformSumsToCNF(vps& sets, MinisatID::PCSolver& pcsolver);

}
}

#endif /* AGGTRANSFORM_HPP_ */
