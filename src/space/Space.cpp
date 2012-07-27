#include "external/Space.hpp"
#include "space/SearchEngine.hpp"
#include "theorysolvers/PCSolver.hpp"
#include "Remapper.hpp"
#include "external/Translator.hpp"
#include "datastructures/InternalAdd.hpp"

using namespace std;
using namespace MinisatID;

Space::Space(const SolverOption& options, bool oneshot) :
		ExternalConstraintVisitor(options, "Space"),
		monitor(new Monitor(getRemapper())), varcreator(new VarCreation(getRemapper())), engine(
				new SearchEngine(new PCSolver(getOptions(), monitor, varcreator, this, oneshot))),
				oneshot(oneshot),
				executed(false) {
}
Space::Space(Remapper* remapper, Translator* translator, const SolverOption& options, bool oneshot) :
		ExternalConstraintVisitor(remapper, translator, options, "Space"),
		monitor(new Monitor(getRemapper())), varcreator(new VarCreation(getRemapper())), engine(
				new SearchEngine(new PCSolver(getOptions(), monitor, varcreator, this, oneshot))),
				oneshot(oneshot),
				executed(false) {
}
Space::~Space() {
	delete (engine);
	delete (monitor);
}

void Space::addMonitor(PropAndBackMonitor* m) {
	monitor->addMonitor(m);
}

void Space::notifyUnsat(){
	engine->notifyUnsat();
}

bool Space::isCertainlyUnsat() const {
	return engine->satState() == SATVAL::UNSAT;
}

bool Space::isOptimizationProblem() const {
	return engine->isOptimizationProblem();
}

bool Space::isAlwaysAtOptimum() const {
	return engine->isAlwaysAtOptimum();
}

void Space::add(const Disjunction& o){
	internalAdd(o, *getEngine());
}
void Space::add(const Implication& o){
	internalAdd(o, *getEngine());
}
void Space::add(const Rule& o){
	internalAdd(o, *getEngine());
}
void Space::add(const WLSet& o){
	internalAdd(o, *getEngine());
}
void Space::add(const Aggregate& o){
	internalAdd(o, *getEngine());
}
void Space::add(const MinimizeOrderedList& o){
	internalAdd(o, *getEngine());
}
void Space::add(const MinimizeSubset& o){
	internalAdd(o, *getEngine());
}
void Space::add(const MinimizeVar& o){
	internalAdd(o, *getEngine());
}
void Space::add(const MinimizeAgg& o){
	internalAdd(o, *getEngine());
}
void Space::add(const Symmetry& o){
	internalAdd(o, *getEngine());
}
void Space::add(const IntVarEnum& o){
	internalAdd(o, *getEngine());
}
void Space::add(const IntVarRange& o){
	internalAdd(o, *getEngine());
}
void Space::add(const CPAllDiff& o){
	internalAdd(o, *getEngine());
}
void Space::add(const CPBinaryRel& o){
	internalAdd(o, *getEngine());
}
void Space::add(const CPCount& o){
	internalAdd(o, *getEngine());
}
void Space::add(const CPBinaryRelVar& o){
	internalAdd(o, *getEngine());
}
void Space::add(const CPSumWeighted& o){
	internalAdd(o, *getEngine());
}
void Space::add(const CPProdWeighted& o){
	internalAdd(o, *getEngine());
}
void Space::add(const CPElement& o){
	internalAdd(o, *getEngine());
}
void Space::add(const LazyGroundLit& o){
	internalAdd(o, *getEngine());
}
void Space::add(const LazyGroundImpl& o){
	internalAdd(o, *getEngine());
}
void Space::add(const LazyAddition& o){
	internalAdd(o, *getEngine());
}
