/****************************************************************
 * Copyright 2010-2012 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat, Stef De Pooter, Johan Wittocx
 * and Bart Bogaerts, K.U.Leuven, Departement Computerwetenschappen,
 * Celestijnenlaan 200A, B-3001 Leuven, Belgium
 ****************************************************************/

#ifndef IDP_FILEMANAGEMENT_HPP_
#define IDP_FILEMANAGEMENT_HPP_

#include <vector>
#include <string>
#include <fstream>

// NOTE: Dirs NEED to and with a forward slash!
std::vector<std::string> getAllFilesInDirs(const std::string& prefix, const std::vector<std::string>& dirs);

template<typename T>
bool fileIsReadable(T* filename) { //quick and dirty
	std::ifstream f(filename, std::ios::in);
	bool exists = f.is_open();
	if (exists) {
		f.close();
	}
	return exists;
}

#endif /* IDP_FILEMANAGEMENT_HPP_ */
