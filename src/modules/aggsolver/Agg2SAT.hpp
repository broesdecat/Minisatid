/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef AGG2SAT_HPP_
#define AGG2SAT_HPP_

#include <vector>
#include <algorithm>

#include "modules/aggsolver/AggProp.hpp"
#include "modules/aggsolver/AggSet.hpp"
#include "modules/aggsolver/AggUtils.hpp"
#include "theorysolvers/PCSolver.hpp"
#include "modules/aggsolver/PartiallyWatched.hpp"

namespace MinisatID{

//Temporary structure to create pseudo booleans
struct PBAgg;

class AggToCNFTransformer;
SATVAL execute(AggToCNFTransformer& transformer);

class AggToCNFTransformer{
private:
	PCSolver& pcsolver;
	std::vector<PBAgg*> pbaggs;
	int maxvar;
	std::map<Atom, Atom> opbinternal2pcsolver;
public:
	AggToCNFTransformer(PCSolver* pcsolver):pcsolver(*pcsolver), maxvar(1){}
	~AggToCNFTransformer();
	void add(WLSet* set, std::vector<TempAgg*>& aggs);

	friend SATVAL execute(AggToCNFTransformer& transformer);
};

}

#endif /* AGG2SAT_HPP_ */
