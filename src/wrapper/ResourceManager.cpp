/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#include "external/ResourceManager.hpp"
#include "GeneralUtils.hpp"

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
	assert(!open || fileptr!=NULL);
	if (!open) {
		open = true;
		fileptr = fopen(name.c_str(), write ? "wb" : "r");
		if (fileptr == NULL) {
			stringstream ss;
			ss <<">> \"" <<name <<"\" is not a valid filename or not readable.\n";
			throw idpexception(ss.str());
		}
	}
	return fileptr;
}

std::streambuf* FileMan::getBuffer() {
	assert(!open || fileptr==NULL);
	if (!open) {
		open = true;
		filebuf.open(name.c_str(), write ? std::ios::out : std::ios::in);
		if (!filebuf.is_open()) {
			stringstream ss;
			ss <<">> \"" <<name <<"\" is not a valid filename or not readable.\n";
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

namespace MinisatID {
	string inputurl = "";
	std::shared_ptr<ResMan> input;
}

void MinisatID::setInputFileUrl(string url) {
	assert(input.get()==NULL);
	inputurl = url;
}

void createInput() {
	if (input.get() == NULL) {
		if (inputurl == "") {
			input = std::shared_ptr<ResMan>(new StdMan(true));
			cerr <<"Reading from standard input...\n";
		} else {
			input = std::shared_ptr<ResMan>(new FileMan(inputurl.c_str(), false));
		}
	}
}

FILE* MinisatID::getInputFile() {
	createInput();
	return input->getFile();
}

std::streambuf* MinisatID::getInputBuffer() {
	createInput();
	return input->getBuffer();
}

void MinisatID::closeInput() {
	if (input.get() != NULL) {
		input->close();
	}
}
