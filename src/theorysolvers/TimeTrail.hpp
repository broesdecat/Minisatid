/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef LITTRAIL_HPP_
#define LITTRAIL_HPP_

#include <cstdio>
#include <map>
#include <set>

#include "utils/Utils.hpp"

namespace MinisatID {

class TimeTrail{
	int 					newesttimepoint;
	std::vector<Lit>		trail;
	std::vector<int>		var2time;
	std::vector<vsize>		decisionlevel2trail;

public:
	TimeTrail(): newesttimepoint(0){
		decisionlevel2trail.push_back(trail.size());
	}
	void notifyPropagate(const Lit& lit) {
		if(var2time.size()<=(vsize)var(lit)){
			var2time.resize(var(lit)+1, -1);
		}
		trail.push_back(lit);
		var2time[(vsize)var(lit)] = newesttimepoint++;
	}
	void notifyNewDecisionLevel(){
		decisionlevel2trail.push_back(trail.size());
	}
	void notifyBacktrack(int untillevel) {
		for(vsize i=decisionlevel2trail[(vsize)untillevel+1]; i<trail.size(); ++i){
			assert(trail.size()>i);
			assert(var2time.size()>(vsize)var(trail[i]));
			var2time[var(trail[i])]=-1;
		}
		trail.resize(decisionlevel2trail[(vsize)untillevel+1]);
		decisionlevel2trail.resize((vsize)untillevel+1);
	}
	bool hasTime(const Lit& lit){
		return var2time.size()>(vsize)var(lit) && var2time[(vsize)var(lit)]!=-1;
	}
	int getTime(const Lit& lit){
		if(!hasTime(lit)){
			return newesttimepoint+1;
		}
		return var2time[(vsize)var(lit)];
	}
};

}

#endif /* LITTRAIL_HPP_ */
