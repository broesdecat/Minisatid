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
#include "satsolver/BasicSATUtils.hpp"
#include "external/Remapper.hpp"

namespace MinisatID{

class Translator;
class PCSolver;
class PropAndBackMonitor;

typedef std::vector<Lit> litlist;

typedef cb::Callback1<std::string, int> callbackprinting; // TODO wrap in translator (goes back to grounder)

class InnerMonitor {
private:
	Remapper* remapper;
	std::vector<PropAndBackMonitor*> monitors;
public:
	InnerMonitor(Remapper* r)
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

template<class Engine>
class ConstraintAdditionInterface{
protected:
	Remapper* remapper;
public:
	ConstraintAdditionInterface(): remapper(new Remapper()){

	}
	~ConstraintAdditionInterface() {
		delete(remapper);
	}

	Remapper& getRemapper() { return *remapper; }
	virtual Engine* getEngine() = 0;
};

class Space: public LiteralPrinter, public ConstraintAdditionInterface<PCSolver>{
private:
	SolverOption basicoptions;
	InnerMonitor* monitor;
	VarCreation* varcreator;
	PCSolver* engine;

public:
	Space(SolverOption options);
	~Space();
	PCSolver* getEngine() { return engine; }
	const SolverOption& getOptions() const { return basicoptions; }

	bool isCertainlyUnsat() const;

	// Printing, might move?
private:
	bool hasprintcallback; // FIXME make all of these a Printer!
	callbackprinting _cb;
	Translator *_translator, *_origtranslator;
public:
	virtual std::string printLiteral(const Lit& lit) const;
	std::string print(const litlist& literals) const;

	void setTranslator(Translator* translator){
		_translator = translator;
	}
	Translator* getTranslator(){
		return _translator;
	}
	void setCallBackTranslator(callbackprinting cb){
		hasprintcallback = true;
		_cb = cb;
	}

	void addMonitor(PropAndBackMonitor* monitor);

	bool isOptimizationProblem() const;
};

}

#endif /* SPACE_HPP_ */
