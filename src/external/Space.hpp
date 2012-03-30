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
#include "satsolver/BasicSATUtils.hpp"

namespace MinisatID{

class Remapper;
class Translator;
class PCSolver;
class PropAndBackMonitor;

typedef std::vector<Lit> litlist;

typedef cb::Callback1<std::string, int> callbackprinting; // TODO wrap in translator (goes back to grounder)

class Space{
private:
	SolverOption basicoptions;
	Remapper* remapper;
	PCSolver* engine;

public:
	Space(SolverOption options);
	Remapper& getRemapper() { return *remapper; }
	PCSolver* getEngine() { return engine; }
	const SolverOption& getOptions() const { return basicoptions; }

	bool isCertainlyUnsat() const;

	// Printing, might move?
private:
	bool hasprintcallback;
	callbackprinting _cb;
	Translator* _translator;
public:
	std::string print(const Lit& lit) const;
	std::string print(const litlist& literals) const;

	void setTranslator(Translator* translator){
		_translator = translator;
	}
	void setCallBackTranslator(callbackprinting cb){
		hasprintcallback = true;
		_cb = cb;
	}

	void addMonitor(PropAndBackMonitor* monitor){
		// FIXME
	}

	bool isOptimizationProblem() const;
};

}

#endif /* SPACE_HPP_ */
