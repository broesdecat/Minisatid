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

#include "Idpexception.hpp"
#include "LiteralPrinter.hpp"
#include "ExternalUtils.hpp"
#include "utils/ContainerUtils.hpp"

namespace MinisatID {

enum FIXEDVAL {
	FIXED_TRUE, FIXED_ARBIT, FIXED_FALSE
};
enum PRINTCHOICE {
	PRINT_FIXED, PRINT_ARBIT
};

struct TupleInterpr {
	FIXEDVAL value;
	std::vector<std::string> arguments;

	TupleInterpr(FIXEDVAL value, const std::vector<std::string>& arg)
			: value(value), arguments(arg) {
	}
};

struct Type {
	std::string name;
	std::vector<std::string> domainelements;

	Type(std::string name, std::vector<std::string> domainelements)
			: name(name), domainelements(domainelements) {
	}
};

struct Symbol {
private:
	std::string name;
public:
	std::string getName(bool fodot) {
		if (fodot) {
			return name;
		} else {
			std::string n = name;
			n.at(0) = tolower(n.at(0));
			return n;
		}
	}
	int startnumber, endnumber;
	std::vector<Type*> types;
	bool isfunction;

	Symbol(std::string name, int startnumber, int endnumber, std::vector<Type*> types, bool isfunction)
			: name(name), startnumber(startnumber), endnumber(endnumber), types(types), isfunction(isfunction) {
	}
};

struct SymbolInterpr {
	Symbol* symbol;
	std::vector<TupleInterpr> tuples;

	SymbolInterpr(Symbol* symbol)
			: symbol(symbol) {
	}
};
typedef std::vector<SymbolInterpr> modelvec;

class Translator: public LiteralPrinter {
public:
	virtual ~Translator() {
	}

	virtual void printModel(std::ostream& output, const Model& model);

	template<typename List> // vector/map/set with pairs of unsigned int and MinisatID::Literal
	void printTranslation(std::ostream& output, const List& l);

	virtual bool hasTranslation(const MinisatID::Lit&) const {
		return false;
	}

	virtual void printCurrentOptimum(std::ostream&, const Weight&) {
	}
	virtual void printHeader(std::ostream&) {
	}

	// Called to guarantee that all data is in a usable state.
	virtual void finish() {
	}
};

class PlainTranslator: public Translator {
public:
	virtual bool hasTranslation(const MinisatID::Lit&) const {
		return true;
	}
};

class FODOTTranslator: public Translator {
private:
	bool tofodot;
	bool finisheddata; //true if the datastructures have been initialized after parsing
	bool emptytrans; //true as long as no predicate has been added to the translator

	int largestnottseitinatom;

	// arbitrary temp information
	bool printedArbitrary;

	// output
	modelvec arbitout, truemodelcombinedout;

	std::map<std::string, Type*> types;
	std::vector<Symbol*> symbols;

	std::vector<int> truelist;
	std::vector<int> arbitlist;
	std::map<Symbol*, bool> symbolasarbitatomlist;

public:
	FODOTTranslator(bool asaspstructure)
			: Translator(), tofodot(not asaspstructure), finisheddata(false), emptytrans(true), largestnottseitinatom(-1), printedArbitrary(false) {
	}

	virtual ~FODOTTranslator() {
		deleteList<Type>(types);
		deleteList<Symbol>(symbols);
	}

	virtual void finish() {
		if (!finisheddata) {
			finishData();
		}
	}

	void setTruelist(const std::vector<int>& vi) {
		truelist = vi;
	}
	void setArbitlist(const std::vector<int>& vi) {
		arbitlist = vi;
	}
	void addType(std::string name, const std::vector<std::string>& inter) {
		types.insert( { name, new Type(name, inter) });
	}
	void addPred(std::string name, int startingnumber, const std::vector<std::string>& typenames, bool isfunction) {
		std::vector<Type*> argtypes;
		int joinsize = 1;
		for (auto i = typenames.cbegin(); i < typenames.cend(); ++i) {
			argtypes.push_back(types.at(*i));
			joinsize *= argtypes.back()->domainelements.size();
		}

		symbols.push_back(new Symbol(name, startingnumber, startingnumber + joinsize - 1, argtypes, isfunction));
		emptytrans = false;
	}

	bool hasTranslation(const MinisatID::Lit& lit) const;

	std::string toString(const Lit& lit) const;
	void printModel(std::ostream& output, const Model& model);
	void printHeader(std::ostream& output) {
		if (!finisheddata) {
			finishParsing(output);
		}

		if (emptytrans) {
			return;
		}
	}

private:
	void finishData();
	void finishParsing(std::ostream& output);
	std::string getPredName(int predn) const;
	void printTuple(const std::vector<std::string>& tuple, std::ostream& output) const {
		bool begin = true;
		for (auto k = tuple.cbegin(); k < tuple.cend(); ++k) {
			if (!begin) {
				output << ",";
			}
			begin = false;
			output << *k;
		}
	}
	void printPredicate(const SymbolInterpr& pred, std::ostream& output, PRINTCHOICE print) const;
	void printFunction(const SymbolInterpr& pred, std::ostream& output, PRINTCHOICE print) const;
	void printInterpr(const modelvec& model, std::ostream& output, PRINTCHOICE print) const;

	struct AtomInfo {
		bool hastranslation;
		uint symbolindex;
		std::vector<std::string> arg;
	};
	AtomInfo deriveStringFromAtomNumber(int atom) const;
};

class OPBPolicy {
public:
	void printLit(std::ostream&, const Lit&, const std::string&){
		throw idpexception("Invalid code path.");
	}
	void printVar(std::ostream& output, const std::string& var, int value){
		output << var << "=(" << value << ") ";
	}
	void printCurrentOptimum(std::ostream& output, const Weight& value);
	void printModelEnd(std::ostream& output){
		output << "\n";
	}
};

class QBFPolicy {
public:
	void printLit(std::ostream& output, const Lit& lit, const std::string& text){
		output <<(lit.hasSign()?"-":"") <<text <<" ";
	}
	void printVar(std::ostream&, const std::string&, int){
		throw idpexception("Invalid code path.");
	}
	void printCurrentOptimum(std::ostream&, const Weight&){
		throw idpexception("Invalid code path.");
	}
	void printModelEnd(std::ostream& output){
		output << "0\n";
	}
};

class LParsePolicy {
public:
	void printLit(std::ostream& output, const Lit& lit, const std::string& text){
		if (not lit.hasSign()) { //Do not print false literals
			output << text << " ";
		}
	}
	void printVar(std::ostream& output, const std::string& var, int value){
		output << var << "=(" << value << ") ";
	}
	void printCurrentOptimum(std::ostream& output, const Weight& value);
	void printModelEnd(std::ostream& output){
		output << "\n";
	}
};

class FZPolicy {
public:
	void printLit(std::ostream& output, const Lit& lit, const std::string& text){
		output <<text <<" = " <<(sign(lit)?"false":"true") <<"\n";
	}
	void printVar(std::ostream& output, const std::string& var, int value){
		output << var << "= " << value << ";\n";
	}
	void printCurrentOptimum(std::ostream& output, const Weight& value);
	void printModelEnd(std::ostream& output){
		output << "----------\n";
	}
};

template<class OptimumPolicy>
class TupleTranslator: public Translator, public OptimumPolicy {
private:
	std::map<Atom, std::string> lit2name;
	std::map<VarID, std::string> var2name;

public:
	TupleTranslator()
			: Translator() {
	}
	virtual ~TupleTranslator() {
	}

	bool hasTranslation(const MinisatID::Lit& lit) const {
		return lit2name.find(lit.getAtom()) != lit2name.cend();
	}

	void addTuple(Atom atom, std::string name) {
		lit2name[atom] = name;
	}

	void addTuple(VarID var, std::string name) {
		var2name[var] = name;
	}

	void printModel(std::ostream& output, const Model& model) {
		for (auto lit : model.literalinterpretations) {
			auto it = lit2name.find(lit.getAtom());
			if(it != lit2name.cend()){
				OptimumPolicy::printLit(output, lit, it->second);
			}
		}
		for (auto vareq : model.variableassignments) {
			auto it = var2name.find(vareq.variable);
			if(it != var2name.cend()){
				OptimumPolicy::printVar(output, it->second, vareq.value);
			}
		}
		OptimumPolicy::printModelEnd(output);
		output.flush();
	}

	std::string toString(VarID var) {
		std::stringstream ss;
		auto it = var2name.find(var);
		if (it != var2name.cend()) {
			ss << (*it).second;
		}
		return ss.str();
	}
	std::string toString(const Lit& lit) {
		std::stringstream ss;
		auto it = lit2name.find(lit.getAtom());
		if (it != lit2name.cend()) {
			ss << (lit.hasSign() ? "-" : "") << (*it).second;
		}
		return ss.str();
	}

	virtual void printCurrentOptimum(std::ostream& output, const Weight& value) {
		OptimumPolicy::printCurrentOptimum(output, value);
	}
};

typedef TupleTranslator<OPBPolicy> OPBTranslator;
typedef TupleTranslator<LParsePolicy> LParseTranslator;
typedef TupleTranslator<QBFPolicy> QBFTranslator;
typedef TupleTranslator<FZPolicy> FZTranslator;

}

#endif /* TRANSLATOR_HPP_ */
