#include "parser/ResourceManager.hpp"

#include <tr1/memory>
#include "external/ExternalUtils.hpp"

using namespace std;
using namespace std::tr1;
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
		fileptr = fopen(name, write ? "wb" : "r");
		if (fileptr == NULL) {
			char s[100];
			sprintf(s, "`%s' is not a valid filename or not readable.\n", name);
			throw idpexception(s);
		}
	}
	return fileptr;
}

std::streambuf* FileMan::getBuffer() {
	assert(!open || fileptr==NULL);
	if (!open) {
		open = true;
		if (!filebuf.open(name, write ? std::ios::out : std::ios::in)) {
			char s[100];
			sprintf(s, "`%s' is not a valid filename or not readable.\n", name);
			throw idpexception(s);
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

///////
// Input/output file management
///////

namespace MinisatID {
string inputurl = "";
string outputurl = "";
std::tr1::shared_ptr<ResMan> input, output;
}

void MinisatID::setInputFileUrl(string url) {
	assert(input.get()==NULL);
	inputurl = url;
}

void MinisatID::setOutputFileUrl(string url) {
	assert(output.get()==NULL);
	outputurl = url;
}

void createInput() {
	if (input.get() == NULL) {
		if (inputurl == "") {
			input = std::tr1::shared_ptr<ResMan>(new StdMan(true));
			report("Reading from standard input...\n");
		} else {
			cerr <<inputurl <<endl;
			input = std::tr1::shared_ptr<ResMan>(new FileMan(inputurl.c_str(), false));
		}
	}
}

void createOutput() {
	if (output.get() == NULL) {
		if (outputurl == "") {
			output = std::tr1::shared_ptr<ResMan>(new StdMan(false));
		} else {
			output = std::tr1::shared_ptr<ResMan>(new FileMan(outputurl.c_str(), true));
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

FILE* MinisatID::getOutputFile() {
	createOutput();
	return output->getFile();
}

std::streambuf* MinisatID::getOutputBuffer() {
	createOutput();
	return output->getBuffer();
}

void MinisatID::closeInput() {
	if (input.get() != NULL) {
		input->close();
	}
}

void MinisatID::closeOutput() {
	if (output.get() != NULL) {
		output->close();
	}
}
