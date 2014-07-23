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
				new SearchEngine(new PCSolver(DEFAULTTHEORYID, getOptions(), monitor, varcreator, this, oneshot))),
				oneshot(oneshot),
				executed(false),
				optim(false) {
}
Space::Space(Remapper* remapper, Translator* translator, const SolverOption& options, bool oneshot) :
		ExternalConstraintVisitor(remapper, translator, options, "Space"),
		monitor(new Monitor(getRemapper())), varcreator(new VarCreation(getRemapper())), engine(
				new SearchEngine(new PCSolver(DEFAULTTHEORYID, getOptions(), monitor, varcreator, this, oneshot))),
				oneshot(oneshot),
				executed(false),
				optim(false) {
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
	return optim;
}

bool Space::isAlwaysAtOptimum() const {
	return engine->isAlwaysAtOptimum();
}

void Space::add(const Disjunction& o){
	internalAdd(o, o.theoryid, *getEngine());
}
void Space::add(const Implication& o){
	internalAdd(o, o.theoryid, *getEngine());
}
void Space::add(const Rule& o){
	internalAdd(o, o.theoryid, *getEngine());
}
void Space::add(const WLSet& o){
	internalAdd(o, o.theoryid, *getEngine());
}
void Space::add(const Aggregate& o){
	internalAdd(o, o.theoryid, *getEngine());
}
void Space::add(const MinimizeOrderedList& o){
	optim = true;
	// TODO disable in other theories (also other optim)
	internalAdd(o, o.theoryid, *getEngine());
}
void Space::add(const MinimizeSubset& o){
	optim = true;
	internalAdd(o, o.theoryid, *getEngine());
}
void Space::add(const OptimizeVar& o){
	optim = true;
	internalAdd(o, o.theoryid, *getEngine());
}
void Space::add(const MinimizeAgg& o){
	optim = true;
	internalAdd(o, o.theoryid, *getEngine());
}
void Space::add(const Symmetry& o){
	internalAdd(o, o.theoryid, *getEngine());
}
void Space::add(const BoolVar& o){
	internalAdd(o, o.theoryid, *getEngine());
}
void Space::add(const IntVarEnum& o){
	internalAdd(o, o.theoryid, *getEngine());
}
void Space::add(const IntVarRange& o){
	internalAdd(o, o.theoryid, *getEngine());
}
void Space::add(const CPAllDiff& o){
	internalAdd(o, o.theoryid, *getEngine());
}
void Space::add(const CPElement& o){
	internalAdd(o, o.theoryid, *getEngine());
}
void Space::add(const CPBinaryRel& o){
	internalAdd(o, o.theoryid, *getEngine());
}
void Space::add(const CPCount& o){
	internalAdd(o, o.theoryid, *getEngine());
}
void Space::add(const CPBinaryRelVar& o){
	internalAdd(o, o.theoryid, *getEngine());
}
void Space::add(const CPSumWeighted& o){
	internalAdd(o, o.theoryid, *getEngine());
}
void Space::add(const CPProdWeighted& o){
	internalAdd(o, o.theoryid, *getEngine());
}
void Space::add(const LazyGroundLit& o){
	internalAdd(o, o.theoryid, *getEngine());
}
void Space::add(const LazyGroundImpl& o){
	internalAdd(o, o.theoryid, *getEngine());
}
void Space::add(const LazyAddition& o){
	internalAdd(o, o.theoryid, *getEngine());
}
void Space::add(const TwoValuedRequirement& o){
	internalAdd(o, o.theoryid, *getEngine());
}
void Space::add(const SubTheory& o){
	internalAdd(o, o.theoryid, *getEngine());
}
void Space::add(const LazyAtom& o){
	internalAdd(o, o.theoryid, *getEngine());
}

Value Space::getTruthValue(const Lit& lit) const {
	auto val = getEngine()->getModelValue(lit);
	if(val==l_True){
		return Value::True;
	}else if(val==l_False){
		return Value::False;
	}else{
		return Value::Unknown;
	}
}

MXStatistics Space::getStats() const{
	return getEngine()->getStats();
}
