/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef MONITORINTERFACE_HPP
#define MONITORINTERFACE_HPP

#include <functional>

#include "external/ExternalUtils.hpp"

#include "callback.hpp"

namespace MinisatID {

class Monitor{
private:
	cb::Callback1<void, int> backtrackcb;
	cb::Callback2<void, Literal, int> propagatedcb;

public:
	void setBacktrackCB(cb::Callback1<void, int> cb){
		backtrackcb = cb;
	}
	void setPropagateCB(cb::Callback2<void, Literal, int> cb){
		propagatedcb = cb;
	}

	void notifyPropagated(Literal lit, int decisionlevel){
		propagatedcb(lit, decisionlevel);
	}

	//Keep all assignments at untillevel, but not beyond
	void notifyBacktracked(int untillevel){
		backtrackcb(untillevel);
	}
};

}

#endif /* MONITORINTERFACE_HPP */
