#pragma once

#include <string>
#include <sstream>
#include "Options.hpp"
#include "Datastructures.hpp"
#include "LiteralPrinter.hpp"

namespace MinisatID {

#define UNHANDLED(constr, visitor) \
	std::stringstream ss;\
 	 ss <<"Handling " <<constr <<" is not handled by " <<visitor <<".";\
 	 throw idpexception(ss.str());

class ConstraintVisitor {
private:
	std::string name;
public:
	ConstraintVisitor(const std::string& name) :
			name(name) {

	}
	virtual ~ConstraintVisitor() {
	}
	std::string getName() const {
		return name;
	}
	virtual void add(const Disjunction&) {
		UNHANDLED("disjunctions", getName())
	}
	virtual void add(const Implication&) {
		UNHANDLED("implications", getName())
	}
	virtual void add(const Rule&) {
		UNHANDLED("rules", getName())
	}
	virtual void add(const WLSet&) {
		UNHANDLED("sets", getName())
	}
	virtual void add(const Aggregate&) {
		UNHANDLED("aggregates", getName())
	}
	virtual void add(const MinimizeSubset&) {
		UNHANDLED("subsetminimization", getName())
	}
	virtual void add(const OptimizeVar&) {
		UNHANDLED("variable optimization", getName())
	}
	virtual void add(const MinimizeAgg&) {
		UNHANDLED("aggregate minimization", getName())
	}
	virtual void add(const BoolVar&) {
		UNHANDLED("boolvar", getName())
	}
	virtual void add(const IntVarEnum&) {
		UNHANDLED("intvar enums", getName())
	}
	virtual void add(const IntVarRange&) {
		UNHANDLED("intvar ranges", getName())
	}
	virtual void add(const CPAllDiff&) {
		UNHANDLED("alldifferent constraints", getName())
	}
	virtual void add(const CPBinaryRel&) {
		UNHANDLED("binary constraints", getName())
	}
	virtual void add(const CPBinaryRelVar&) {
		UNHANDLED("binary var constraints", getName())
	}
	virtual void add(const CPSumWeighted&) {
		UNHANDLED("weighted sum constraints", getName())
	}
	virtual void add(const CPProdWeighted&) {
		UNHANDLED("weighted prod constraints", getName())
	}
	virtual void add(const LazyGroundLit&) {
		UNHANDLED("lazy residuals", getName())
	}
	virtual void add(const LazyGroundImpl&) {
		UNHANDLED("lazy implications", getName())
	}
	virtual void add(const LazyAddition&) {
		UNHANDLED("lazy implication additions", getName())
	}
	virtual void add(const TwoValuedRequirement&) {
		UNHANDLED("Twovalued requirement", getName())
	}
	virtual void add(const TwoValuedVarIdRequirement&) {
		UNHANDLED("Twovaluedvarid requirement", getName())
	}
	virtual void add(const SubTheory&) {
		UNHANDLED("Subtheory", getName())
	}
	virtual void add(const LazyAtom&) {
		UNHANDLED("Lazy atom", getName())
	}
};

class Translator;
class ExternalConstraintVisitor: public LiteralPrinter, public ConstraintVisitor {
private:
	SolverOption basicoptions;
	Remapper* remapper, *_origremapper;
public:
	ExternalConstraintVisitor(const SolverOption& options, const std::string& name);
	ExternalConstraintVisitor(Remapper* remapper, Translator *translator, const SolverOption& options, const std::string& name);
	virtual ~ExternalConstraintVisitor();

	Remapper* getRemapper() const {
		return remapper;
	}

	virtual void notifyUnsat(){}

private:
	Translator *_translator, *_origtranslator;
	std::map<Atom,std::string> atom2string;
public:
	virtual void setString(const Atom& lit, const std::string& name);
	virtual bool isTseitin(const Atom&) const;
	virtual std::string toString(VarID id) const;
	virtual std::string toString(const Lit& lit) const;
	std::string toString(const litlist& literals) const;

	void setTranslator(Translator* translator) {
		_translator = translator;
	}
	Translator* getTranslator() const {
		return _translator;
	}

	const SolverOption& getOptions() const {
		return basicoptions;
	}

	virtual bool isCertainlyUnsat() const {
		return false;
	}
	void notifyFinishParsing();

	virtual void finishParsing() {}
};

}
