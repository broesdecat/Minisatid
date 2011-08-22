/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef TRANSLATOR_HPP_
#define TRANSLATOR_HPP_

#include <vector>
#include <string>
#include <map>
#include <ostream>
#include <sstream>

#include <algorithm>

#include <GeneralUtils.hpp>
#include <utils/Print.hpp>

#include <external/SolvingMonitor.hpp>

#include "external/ExternalUtils.hpp"

namespace MinisatID {

class Model;

enum FIXEDVAL { FIXED_TRUE, FIXED_ARBIT, FIXED_FALSE };
enum PRINTCHOICE { PRINT_FIXED, PRINT_ARBIT };

struct TupleInterpr{
	FIXEDVAL value;
	std::vector<std::string> arguments;

	TupleInterpr(FIXEDVAL value, const std::vector<std::string>& arg): value(value), arguments(arg){}
};

struct Type{
	std::string name;
	std::vector<std::string> domainelements;

	Type(std::string name, std::vector<std::string> domainelements): name(name), domainelements(domainelements){}
};

struct Symbol{
private:
	std::string name;
public:
	std::string getName(bool fodot){
		if(fodot){
			return name;
		}else{
			std::string n = name;
			n.at(0)=tolower(n.at(0));
			return n;
		}
	}
	int startnumber, endnumber;
	std::vector<Type*> types;
	bool isfunction;

	Symbol(std::string name, int startnumber, int endnumber, std::vector<Type*> types, bool isfunction):
		name(name), startnumber(startnumber), endnumber(endnumber), types(types), isfunction(isfunction){}
};

struct SymbolInterpr{
	Symbol* symbol;
	std::vector<TupleInterpr> tuples;

	SymbolInterpr(Symbol* symbol): symbol(symbol){}
};
typedef std::vector<SymbolInterpr> modelvec;

class Translator {
public:
	Translator(){}
	virtual ~Translator(){}


	virtual void	printModel			(std::ostream& output, const Model& model){
		std::stringstream ss;
		for (std::vector<Literal>::const_iterator i = model.literalinterpretations.begin(); i < model.literalinterpretations.end(); ++i){
			ss <<(((*i).hasSign()) ? "-" : "") <<(*i).getAtom().getValue() <<" ";
		}
		for (std::vector<VariableEqValue>::const_iterator i = model.variableassignments.begin(); i < model.variableassignments.end(); ++i){
			ss <<(*i).variable <<"=" <<(*i).value <<" ";
		}
		ss << "0\n";
		//TODO start critical section
		output <<ss.str();
		// end critical section
		output.flush();
	}

	virtual void	printLiteral		(std::ostream& output, const MinisatID::Literal& lit){}
	virtual void 	printCurrentOptimum	(std::ostream& output, const Weight& value){}
	virtual void	printHeader			(std::ostream& output){}

	virtual bool	hasTseitinKnowledge	() const { return false; }
	virtual Atom	smallestTseitinAtom	() { assert(false); return Atom(0); }
};

class FODOTTranslator: public Translator{
private:
	bool tofodot;
	bool finisheddata; //true if the datastructures have been initialized after parsing
	bool emptytrans; //true as long as no predicate has been added to the translator

	int largestnottseitinatom;

	// arbitrary temp information
	bool printedArbitrary;

	// output
	modelvec arbitout, truemodelcombinedout;

	std::map<std::string,Type*>	types;
	std::vector<Symbol*>		symbols;

	std::vector<int>			truelist;
	std::vector<int>			arbitlist;
	std::map<Symbol*,bool>		symbolasarbitatomlist;

public:
	FODOTTranslator(OUTPUTFORMAT fodot): Translator(),
			tofodot(fodot==TRANS_FODOT), finisheddata(false), emptytrans(true),
			largestnottseitinatom(-1),
			printedArbitrary(false){
		assert(fodot!=TRANS_PLAIN);
	}

	virtual ~FODOTTranslator() {
		deleteList<Type>(types);
		deleteList<Symbol>(symbols);
	}

	void	setTruelist		(const std::vector<int>& vi) { truelist = vi;}
	void 	setArbitlist	(const std::vector<int>& vi) { arbitlist = vi;}
	void addType(std::string name, const std::vector<std::string>& inter){
		types.insert(std::pair<std::string,Type*>(name, new Type(name, inter)));
	}
	void addPred(std::string name, int startingnumber, const std::vector<std::string>& typenames, bool isfunction){
		std::vector<Type*> argtypes;
		int joinsize = 1;
		for(std::vector<std::string>::const_iterator i = typenames.begin(); i < typenames.end(); ++i) {
			argtypes.push_back(types.at(*i));
			joinsize *= argtypes.back()->domainelements.size();
		}

		symbols.push_back(new Symbol(name, startingnumber, startingnumber+joinsize-1, argtypes, isfunction));
		emptytrans = false;
	}

	void 	printLiteral		(std::ostream& output, const MinisatID::Literal& lit);
	void 	printModel			(std::ostream& output, const Model& model);
	void 	printHeader			(std::ostream& output){
		if(!finisheddata){
			finishParsing(output);
		}

		if(emptytrans){
			return;
		}
	}

	bool	hasTseitinKnowledge	() const { return true; }
	Atom	smallestTseitinAtom	() { assert(hasTseitinKnowledge()); finishData(); return Atom(largestnottseitinatom+1); }

private:
	void 	finishData		();
	void 	finishParsing	(std::ostream& output);
	std::string getPredName	(int predn) const;
	void printTuple(const std::vector<std::string>& tuple, std::ostream& output) const{
		bool begin = true;
		for(std::vector<std::string>::const_iterator k = tuple.begin(); k < tuple.end(); ++k) {
			if(!begin){
				output << ",";
			}
			begin = false;
			output << *k;
		}
	}
	void 	printPredicate	(const SymbolInterpr& pred, std::ostream& output, PRINTCHOICE print)	const;
	void 	printFunction	(const SymbolInterpr& pred, std::ostream& output, PRINTCHOICE print)	const;
	void 	printInterpr	(const modelvec& model, std::ostream& output, PRINTCHOICE print)	const;

	struct AtomInfo{
		bool hastranslation;
		uint symbolindex;
		std::vector<std::string> arg;
	};
	AtomInfo deriveStringFromAtomNumber(int atom) const;
};

class LParseTranslator: public Translator {
private:
	std::map<Atom,std::string>	lit2name;

public:
	LParseTranslator():Translator(){}
	virtual ~LParseTranslator(){}

	void addTuple(Atom atom, std::string name) {
		lit2name[atom]=name;
	}

	void printModel(std::ostream& output, const Model& model) {
		for(std::vector<Literal>::const_iterator i=model.literalinterpretations.begin(); i<model.literalinterpretations.end(); ++i){
			if(!(*i).hasSign()){ //Do not print false literals
				std::map<Atom, std::string>::const_iterator it = lit2name.find((*i).getAtom());
				if(it!=lit2name.end()){
					output <<(*it).second <<" ";
				}
			}
		}
		output <<"\n";
		output.flush();
		assert(model.variableassignments.size()==0);
	}

	void printLiteral(std::ostream& output, const Literal& lit) {
		std::map<Atom, std::string>::const_iterator it = lit2name.find(lit.getAtom());
		if(it!=lit2name.end()){
			output <<(lit.hasSign()?"~":"") <<(*it).second <<"\n";
		}
	}
};

class OPBTranslator: public Translator {
private:
	std::map<Atom,std::string>	lit2name;

public:
	OPBTranslator():Translator(){}
	virtual ~OPBTranslator(){}

	void addTuple(Atom atom, std::string name){
		lit2name[atom]=name;
	}

	void printModel(std::ostream& output, const Model& model) {
		output <<"v ";
		for(std::vector<Literal>::const_iterator i=model.literalinterpretations.begin(); i<model.literalinterpretations.end(); ++i){
			std::map<Atom, std::string>::const_iterator it = lit2name.find((*i).getAtom());
			if(it!=lit2name.end()){
				if((*i).hasSign()){
					output <<"-";
				}
				output <<(*it).second <<" ";
			}
		}
		output <<"\n";
		output.flush();
		assert(model.variableassignments.size()==0);
	}

	virtual void printCurrentOptimum(std::ostream& output, const Weight& value){
		output <<"o " <<value <<std::endl; // NOTE: has to FLUSH after each print!
	}
};

}

#endif /* TRANSLATOR_HPP_ */
