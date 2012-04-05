/************************************
	Space.hpp
	this file belongs to GidL 2.0
	(c) K.U.Leuven
************************************/

#ifndef SPACE_HPP_
#define SPACE_HPP_

#include <vector>
#include "Options.hpp"
#include "callback.hpp"
#include "constraintvisitors/LiteralPrinter.hpp"
#include "external/Remapper.hpp"
#include "ConstraintAdditionInterface.hpp"

namespace MinisatID{

class Translator;
class PCSolver;
class PropAndBackMonitor;

typedef std::vector<Lit> litlist;

class Monitor {
private:
	Remapper* remapper;
	std::vector<PropAndBackMonitor*> monitors;
public:
	Monitor(Remapper* r)
			: remapper(r) {
	}
	void addMonitor(PropAndBackMonitor* monitor) {
		monitors.push_back(monitor);
	}
	void notifyMonitor(const Lit& propagation, int decisionlevel);
	void notifyMonitor(int untillevel);
};

class VarCreation {
private:
	Remapper* remapper;
public:
	VarCreation(Remapper* r)
			: remapper(r) {
	}
	Var createVar();
};

class Space: public LiteralPrinter, public ConstraintAdditionInterface<PCSolver>{
private:
	SolverOption basicoptions;
	Monitor* monitor;
	VarCreation* varcreator;
	PCSolver* engine;

public:
	Space(SolverOption options);
	~Space();
	PCSolver* getEngine() { return engine; }
	const SolverOption& getOptions() const { return basicoptions; }

	bool isCertainlyUnsat() const;

private:
	Translator *_translator, *_origtranslator;
public:
	virtual std::string toString(const Lit& lit) const;
	std::string toString(const litlist& literals) const;

	void setTranslator(Translator* translator){
		_translator = translator;
	}
	Translator* getTranslator() const {
		return _translator;
	}
	void addMonitor(PropAndBackMonitor* monitor);

	bool isOptimizationProblem() const;
};

}

#endif /* SPACE_HPP_ */
