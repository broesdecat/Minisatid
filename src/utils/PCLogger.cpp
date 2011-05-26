/*
 * PCLogger.cpp
 *
 *  Created on: May 26, 2011
 *      Author: broes
 */

#include "utils/PCLogger.hpp"

PCLogger::PCLogger(): propagations(0){
}

void PCLogger::addCount(Var v) {
	assert(v>=0);
	uint var(v);
	if((var+1)>occurrences.size()){
		occurrences.resize(var+1, 0);
	}
	++occurrences[var];
}

int PCLogger::getCount(Var v) const {
	assert(v>=0);
	return (uint)v>occurrences.size()?0:occurrences.at((uint)v);
}
