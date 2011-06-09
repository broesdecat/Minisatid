/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#include "modules/AggSolver.hpp"

#include "utils/Utils.hpp"
#include "utils/Print.hpp"

#include "modules/aggsolver/AggPrint.hpp"

#include "theorysolvers/PCSolver.hpp"

#include "modules/IDSolver.hpp"

#include "modules/aggsolver/AggPrint.hpp"
#include "modules/aggsolver/AggUtils.hpp"
#include "modules/aggsolver/AggTransform.hpp"

#include "modules/aggsolver/FullyWatched.hpp"
#include "modules/aggsolver/PartiallyWatched.hpp"

#include "utils/Print.hpp"

#include <algorithm>

#include "utils/IntTypes.h"
#include <cmath>

using namespace std;
using namespace MinisatID;

Var	AggSolver::notifyBranchChoice(const Var& chosenvar) const{
	assert(modes().useaggheur);
	if(heurvars.find(chosenvar)!=heurvars.end()){
		for(vector<VI>::const_iterator i=varwithheurval.begin(); i<varwithheurval.end(); i++){
			if((*i).var==chosenvar){
				break;
			}else if(value((*i).var)==l_Undef){
				return (*i).var;
			}
		}
	}
	return chosenvar;
}

void AggSolver::adaptAggHeur(const vwl& wls, int nbagg){
	if(!modes().useaggheur){
		return;
	}
	int heur = 1;
	vwl wlstemp = wls;
	sort(wlstemp.begin(), wlstemp.end(), compareWLByAbsWeights); //largest numbers last
	for(vwl::const_iterator i=wlstemp.begin(); i<wlstemp.end(); i++){
		Var v = var((*i).getLit());
		set<Var>::iterator it = heurvars.find(v);
		if(it==heurvars.end()){
			heurvars.insert(v);
			for(vector<VI>::iterator j=varwithheurval.begin(); j<varwithheurval.end(); j++){
				if((*j).var == v){
					(*j).heurval += heur*nbagg;
					break;
				}
			}
		}else{
			VI vi;
			vi.var = v;
			vi.heurval = heur * nbagg;
			varwithheurval.push_back(vi);
		}
		heur++;
	}
}
