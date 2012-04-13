/****************************************************************
 * Copyright 2010-2012 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat, Stef De Pooter, Johan Wittocx
 * and Bart Bogaerts, K.U.Leuven, Departement Computerwetenschappen,
 * Celestijnenlaan 200A, B-3001 Leuven, Belgium
 ****************************************************************/

#include "external/utils/FileManagement.hpp"
#include <dirent.h>
#include <iostream>

using namespace std;

vector<string> getAllFilesInDirs(const std::string& prefix, const vector<string>& testdirs) {
	vector<string> files;
	DIR *dir;
	struct dirent *ent;
	for (auto currTestDir = testdirs.cbegin(); currTestDir != testdirs.cend(); ++currTestDir) {
		dir = opendir((prefix + (*currTestDir)).c_str());
		if (dir != NULL) {
			while ((ent = readdir(dir)) != NULL) {
				if (ent->d_name[0] != '.') {
					files.push_back(prefix + (*currTestDir) + ent->d_name);
				}
			}
			closedir(dir);
		} else {
			clog << "FAIL    |  Could not open directory " << *currTestDir << "\n.";
		}
	}
	return files;
}
