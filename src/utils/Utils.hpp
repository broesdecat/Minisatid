/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef UTILS_H_
#define UTILS_H_

#include <cstdio>
#include <cstdlib>
#include <vector>
#include <map>

#include "satsolver/SATUtils.hpp"
#include "external/ExternalUtils.hpp"

typedef unsigned int uint;

namespace MinisatID {

enum class VARHEUR { DECIDE, DONT_DECIDE};

class InterMediateDataStruct{
private:
	int offset;
	std::vector<int> seen;

public:
	InterMediateDataStruct(int nbvars, int offset):offset(offset){
		seen.resize(nbvars, 0);
	}

	bool hasElem(Atom var) const { return var-offset>=0 && ((uint)var-offset)<seen.size(); }

	int& getElem(Atom var) { return seen[var-offset]; }
	const int& getElem(Atom var) const { return seen[var-offset]; }
};

enum PRIORITY { FASTEST = 0, FAST = 1, SLOW = 2 };
enum EVENT { EV_PROPAGATE, EV_BACKTRACK, EV_DECISIONLEVEL, EV_BOUNDSCHANGE, EV_MODELFOUND};

class GenWatch{
private:
	bool _innet;
public:
	GenWatch(): _innet(false){}
	virtual ~GenWatch(){}
	virtual void propagate() = 0;
	virtual const Lit& getPropLit() const = 0;
	virtual bool dynamic() const = 0;
	bool isInNetwork() const {
		return _innet;
	}
	void addToNetwork() {
		_innet = true;
	}
	void removeFromNetwork() {
		_innet = false;
	}
};

}

#endif /* UTILS_H_ */
