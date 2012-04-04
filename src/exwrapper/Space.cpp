#include "external/Space.hpp"
#include "theorysolvers/PCSolver.hpp"
#include "external/Remapper.hpp"
#include "external/Translator.hpp"

using namespace std;
using namespace MinisatID;

string Space::toString(const Lit& l) const {
	stringstream ss;
	auto r = *remapper;
	if (r.wasInput(var(l))) {
		auto lit = r.getLiteral(l);
		if (hasprintcallback) {
			auto v = var(lit);
			if(lit.hasSign()){
				v = -v;
			}
			ss << _cb(v);
		} else {
			ss << (lit.hasSign() ? "-" : "") << var(lit)+1;
		}
	} else {
		ss << (sign(l) ? "-" : "") << "intern_" << var(l) + 1; // NOTE: do not call <<l, this will cause an infinite loop (as that calls this method!)
	}
	return ss.str();
}
string Space::toString(const litlist& literals) const {
	stringstream ss;
	bool begin = true;
	for (auto i = literals.cbegin(); i < literals.cend(); ++i) {
		if (not begin) {
			ss << " | ";
		}
		begin = false;
		ss << toString(*i);
	}
	return ss.str();
}

Space::Space(SolverOption modes) :
		basicoptions(modes), hasprintcallback(false), monitor(new Monitor(remapper)), varcreator(new VarCreation(remapper)), engine(
				new PCSolver(modes, monitor, varcreator, this)), _translator(new Translator()) {
	_origtranslator = _translator;
}
Space::~Space() {
	delete (engine);
	delete (monitor);
	delete (varcreator);
	delete (_origtranslator);
}

void Space::addMonitor(PropAndBackMonitor* m) {
	monitor->addMonitor(m);
}

bool Space::isCertainlyUnsat() const {
	return engine->satState() == SATVAL::UNSAT;
}

bool Space::isOptimizationProblem() const {
	return engine->isOptimizationProblem();
}
