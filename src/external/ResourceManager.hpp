/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef RESOURCEMANAGER_HPP_
#define RESOURCEMANAGER_HPP_

#include <stdlib.h>
#include <assert.h>

#include <iostream>
#include <fstream>
#include <string>
#include <tr1/memory>

namespace MinisatID{

//Classes to manage a resource
class ResMan {
private:
	ResMan(const ResMan &);
	ResMan & operator=(const ResMan &);

protected:
	ResMan(){}

public:
	virtual ~ResMan() {	}

	virtual void			close		() = 0;
	virtual FILE* 			getFile		() = 0;
	virtual std::streambuf*	getBuffer	() = 0;
};

//Manage input file
class FileMan: public ResMan {
private:
	bool open, write;
	const char* name;
	FILE* fileptr;
	std::filebuf filebuf;

	FileMan(const FileMan &);
	FileMan & operator=(const FileMan &);

public:
	FileMan(const char* name, bool write) : open(false), write(write), name(name), fileptr(NULL) { }

	~FileMan() { close(); }

	void close();
	FILE* getFile();
	std::streambuf* getBuffer();
};

//Manages input/output via the stdstreams
class StdMan: public ResMan {
private:
	bool in;

	StdMan(const StdMan &);
	StdMan & operator=(const StdMan &);

public:
	StdMan(bool in)	: in(in) {}
	~StdMan() { }

	void close() { }
	FILE* getFile();
	std::streambuf* getBuffer();
};

void setInputFileUrl(std::string url);
void setOutputFileUrl(std::string url);
FILE* getInputFile();
std::streambuf* getInputBuffer();
FILE* getOutputFile();
std::streambuf* getOutputBuffer();
std::tr1::shared_ptr<ResMan> getOutputResMan();
void closeInput();
void closeOutput();

}

#endif /* RESOURCEMANAGER_HPP_ */
