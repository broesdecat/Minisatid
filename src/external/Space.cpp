#include "Space.hpp"
#include "theorysolvers/PCSolver.hpp"
#include "Remapper.hpp"

using namespace std;
using namespace MinisatID;

string Space::print(const Lit& l) const {
	stringstream ss;
	auto r = *remapper;
	if (canBackMapLiteral(l,r) && hasprintcallback) {
		ss << _cb(r.getLiteral(l).getValue());
	} else if (canBackMapLiteral(l,r)) {
		auto lit = r.getLiteral(l);
		ss << (lit.hasSign()?"-":"") << lit.getValue();
	} else {
		ss << (sign(l) ? "-" : "") << "intern_" << var(l) + 1; // NOTE: do not call <<l, this will cause an infinite loop (as that calls this method!)
	}
	return ss.str();
}
string Space::print(const litlist& literals) const {
	stringstream ss;
	bool begin = true;
	for (auto i = literals.cbegin(); i < literals.cend(); ++i) {
		if (not begin) {
			ss << " | ";
		}
		begin = false;
		ss << print(*i);
	}
	return ss.str();
}

Space::Space(SolverOption modes): basicoptions(modes), remapper(new Remapper()), engine(new PCSolver(modes)), monitor(new InnerMonitor(remapper)){
	getEngine()->setMonitor(monitor);
}
Space::~Space(){
	delete(remapper);
	delete(engine);
	delete(monitor);
}

void Space::addMonitor(PropAndBackMonitor* m){
	monitor->addMonitor(m);
}

bool Space::isCertainlyUnsat() const{
	return engine->satState()==SATVAL::UNSAT;
}

bool Space::isOptimizationProblem() const{
	return engine->isOptimizationProblem();
}
