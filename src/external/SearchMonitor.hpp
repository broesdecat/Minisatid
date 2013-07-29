/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#pragma once

#include <functional>
#include "ExternalUtils.hpp"

namespace MinisatID {

/**
 * Class which monitors actions during the propagation/search and notifies its registered callbacks.
 */
class PropAndBackMonitor{
private:
	std::function<void(int)> backtrackcb;
	std::function<void(Lit, int)> propagatedcb;

public:
	void setBacktrackCB(std::function<void(int)> cb){
		backtrackcb = cb;
	}
	void setPropagateCB(std::function<void(Lit, int)> cb){
		propagatedcb = cb;
	}

	void notifyPropagated(const Lit& lit, int decisionlevel){
		propagatedcb(lit, decisionlevel);
	}

	//Keep all assignments at untillevel, but not beyond
	void notifyBacktracked(int untillevel){
		backtrackcb(untillevel);
	}
};

}
