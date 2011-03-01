/* * Copyright 2007-2011 Katholieke Universiteit Leuven * * Use of this software is governed by the GNU LGPLv3.0 license * * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium */
#ifndef TRANSLATOR_HPP_
#define TRANSLATOR_HPP_

#include <vector>
#include <string>
#include <map>
#include <ostream>

#include "external/ExternalUtils.hpp"

namespace MinisatID {
enum FIXEDVAL { FIXED_TRUE, FIXED_ARBIT, FIXED_FALSE };enum PRINTCHOICE { PRINT_FIXED, PRINT_ARBIT };struct TupleInterpr{	FIXEDVAL value;	std::vector<std::string> arguments;	TupleInterpr(FIXEDVAL value, const std::vector<std::string>& arg): value(value), arguments(arg){}};struct SymbolInterpr{	std::string predname;	std::vector<TupleInterpr> tuples;	SymbolInterpr(std::string predname): predname(predname){}};
typedef std::vector<SymbolInterpr> modelvec;

class Translator {
protected:
	// counters
	mutable int modelcounter;

public:
	Translator();
	virtual ~Translator(){}

	virtual void	printLiteral		(std::ostream& output, const MinisatID::Literal& lit);
	virtual void	printModel			(std::ostream& output, const std::vector<Literal>& model);	virtual void 	printCurrentOptimum	(std::ostream& output, const Weight& value);
	virtual void	printHeader			(std::ostream& output);
};

class FODOTTranslator: public Translator{
private:
	bool tofodot;
	bool finisheddata; //true if the datastructures have been initialized after parsing
	bool emptytrans; //true as long as no predicate has been added to the translator

	int largestnottseitinatom;

	// output
	modelvec trueout, arbitout, truemodelcombinedout;

	// Look-up tables
	std::map<std::string,int>	type_lookup;

	// data structures
	std::vector<std::vector<std::string> >	types;
	std::vector<std::vector<int> >	predtypes;
	std::vector<std::string>	predicates;
	std::vector<int>			lowestvalue;
	std::vector<int>			highestvalue;
	std::vector<int>			truelist;
	std::vector<int>			arbitlist;
	std::vector<bool>			isfunc;

	std::vector<std::string> 	arbitatoms;

public:
			FODOTTranslator	(OUTPUTFORMAT fodot);
	virtual ~FODOTTranslator();

	void	setTruelist		(const std::vector<int>& vi) { truelist = vi;}
	void 	setArbitlist	(const std::vector<int>& vi) { arbitlist = vi;}
	void 	addType			(std::string name, const std::vector<std::string>& inter);
	void 	addPred			(std::string name, int num, const std::vector<std::string>& ptypes, bool f);

	void 	printLiteral		(std::ostream& output, const MinisatID::Literal& lit);
	void 	printModel			(std::ostream& output, const std::vector<Literal>& model);
	void 	printHeader			(std::ostream& output);

private:
	void 	finishParsing	(std::ostream& output);
	std::string getPredName	(int predn) const;
	void 	printTuple		(const std::vector<std::string>& tuple, std::ostream& output) 	const;
	void 	printPredicate	(int n, const modelvec& model, std::ostream& output, PRINTCHOICE print)	const;
	void 	printFunction	(int n, const modelvec& model, std::ostream& output, PRINTCHOICE print)	const;	void 	printInterpr	(const modelvec& model, std::ostream& output, PRINTCHOICE print)	const;
	bool 	deriveStringFromAtomNumber(int atom, uint& currpred, std::vector<std::string>& arg) const;
};

class LParseTranslator: public Translator {
private:
	std::map<Atom,std::string>	lit2name;

public:
			LParseTranslator():Translator(){}
	virtual ~LParseTranslator(){}

	void 	addTuple		(Atom atom, std::string name);

	void 	printLiteral	(std::ostream& output, const MinisatID::Literal& lit);
	void 	printModel		(std::ostream& output, const std::vector<Literal>& model);
	void 	printHeader		(std::ostream& output);
};class OPBTranslator: public Translator {private:	std::map<Atom,std::string>	lit2name;public:			OPBTranslator():Translator(){}	virtual ~OPBTranslator(){}	void 	addTuple		(Atom atom, std::string name);	void 	printLiteral		(std::ostream& output, const MinisatID::Literal& lit);	void 	printModel			(std::ostream& output, const std::vector<Literal>& model);	void 	printCurrentOptimum	(std::ostream& output, const Weight& value);	void 	printHeader			(std::ostream& output);};

}

#endif /* TRANSLATOR_HPP_ */
