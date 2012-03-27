/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef MINISATID_FILEUTILS_HPP_
#define MINISATID_FILEUTILS_HPP_

#include <fstream>

namespace MinisatID {

template<class T>
bool fileIsReadable(T* filename) { //quick and dirty
	std::ifstream f(filename, std::ios::in);
	bool exists = f.is_open();
	if (exists) {
		f.close();
	}
	return exists;
}

}

#endif //MINISATID_FILEUTILS_HPP_
