/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef MINISATID_TIMINGUTILS_HPP_
#define MINISATID_TIMINGUTILS_HPP_

namespace MinisatID {
	//In elapsed seconds, taking abstraction of other processes running on the system
	double cpuTime(void);
}

#endif /* MINISATID_TIMINGUTILS_HPP_ */
