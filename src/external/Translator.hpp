/*
 * Translator.hpp
 *
 *  Created on: Jan 10, 2011
 *      Author: broes
 */

#ifndef TRANSLATOR_HPP_
#define TRANSLATOR_HPP_

#include <vector>
#include <string>
#include <map>
#include <ostream>

namespace MinisatID {

enum MODE { TRANS_ARBIT, TRANS_TRUE, TRANS_MODEL };
typedef std::vector<std::vector<std::vector<std::string> > > modelvec;

class Translator {
public:
	Translator();
	virtual ~Translator(){}

	virtual void printModel(std::ostream& output, const std::vector<int>& model) = 0;
	virtual void printHeader(std::ostream& output) = 0;
};

class FODOTTranslator: public Translator{
private:
	bool tofodot;

	// Look-up tables
	std::map<std::string,int>	type_lookup;

	// data structures
	std::vector<std::vector<std::string> >	types;
	std::vector<std::string>		predicates;
	std::vector<std::vector<int> >	predtypes;
	std::vector<int>	lowestvalue;
	std::vector<int>	highestvalue;
	std::vector<int>	truelist;
	std::vector<int>	arbitlist;
	std::vector<bool>	isfunc;

	// output
	modelvec trueout, arbitout, modelout, truemodelcombinedout;

	std::vector<std::string> arbitatoms;

	// counters
	int modelcounter;
	int largestnottseitinatom;

public:
	FODOTTranslator(bool fodot);
	virtual ~FODOTTranslator();

	void setTruelist(const std::vector<int>& vi) { truelist = vi;}
	void setArbitlist(const std::vector<int>& vi) { arbitlist = vi;}
	void addType(std::string name, const std::vector<std::string>& inter);
	void addPred(std::string name, int num, const std::vector<std::string>& ptypes, bool f);

	void printModel(std::ostream& output, const std::vector<int>& model);
	void printHeader(std::ostream& output);

private:
	std::string getPredName(int predn);
	void printTuple(const std::vector<std::string>& tuple, std::ostream& output);
	void printPredicate(int n, const modelvec& model, MODE mode, std::ostream& output);
	void printFunction(int n, const modelvec& model, std::ostream& output);
	void printInterpr(const modelvec& model, MODE mode, std::ostream& output);
	bool deriveStringFromAtomNumber(int atom, int& currpred, std::vector<std::string>& arg);
};

class LParseTranslator: public Translator {
private:
	std::map<int,std::string>	lit2name;

public:
	LParseTranslator():Translator(){}
	virtual ~LParseTranslator(){}

	void addTuple(int lit, std::string name);

	void printModel(std::ostream& output, const std::vector<int>& model);
	void printHeader(std::ostream& output);
};

}

#endif /* TRANSLATOR_HPP_ */
