/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#include "external/utils/ResourceManager.hpp"
#include "external/ExternalUtils.hpp"

#include <memory>
#include <sstream>

using namespace std;
using namespace MinisatID;

void FileMan::close() {
	if (open) {
		open = false;
		if (fileptr == NULL) {
			filebuf.close();
		} else {
			fclose(fileptr);
			fileptr = NULL;
		}
	}
}

FILE* FileMan::getFile() {
	MAssert(!open || fileptr!=NULL);
	if (!open) {
		open = true;
		fileptr = fopen(name.c_str(), write ? "wb" : "r");
		if (fileptr == NULL) {
			stringstream ss;
			ss << ">> \"" << name << "\" is not a valid filename or not readable.\n";
			throw idpexception(ss.str());
		}
	}
	return fileptr;
}

std::streambuf* FileMan::getBuffer() {
	MAssert(!open || fileptr==NULL);
	if (!open) {
		open = true;
		filebuf.open(name.c_str(), write ? std::ios::out : std::ios::in);
		if (!filebuf.is_open()) {
			stringstream ss;
			ss << ">> \"" << name << "\" is not a valid filename or not readable.\n";
			throw idpexception(ss.str());
		}
	}
	return &filebuf;
}

FILE* StdMan::getFile() {
	if (in) {
		return stdin;
	} else {
		return stdout;
	}
}

std::streambuf* StdMan::getBuffer() {
	if (in) {
		return std::cin.rdbuf();
	} else {
		return std::cout.rdbuf();
	}

}

// Input/output file management

std::shared_ptr<ResMan> createInput(const std::string& url) {
	if (url == "") {
		clog << "Reading from standard input...\n";
		return std::shared_ptr<ResMan>(new StdMan(true));
	} else {
		return std::shared_ptr<ResMan>(new FileMan(url.c_str(), false));
	}
}

std::shared_ptr<ResMan> MinisatID::getInput(const std::string& url) {
	return createInput(url);
}

std::shared_ptr<ResMan> MinisatID::createResMan(const std::string& file) {
	std::shared_ptr<ResMan> resman;
	if (file == "") {
		resman = std::shared_ptr<ResMan>(new StdMan(false));
	} else {
		resman = std::shared_ptr<ResMan>(new FileMan(file.c_str(), true));
	}
	return resman;
}
