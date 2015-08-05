#include "external/Space.hpp"
#include "space/SearchEngine.hpp"
#include "theorysolvers/PCSolver.hpp"
#include "Remapper.hpp"
#include "external/Translator.hpp"
#include "datastructures/InternalAdd.hpp"
#include "external/Tasks.hpp"
#include "external/Constraints.hpp"

using namespace std;
using namespace MinisatID;

Space::Space(const SolverOption& options, bool oneshot) :
		ExternalConstraintVisitor(options, "Space"),
		monitor(new Monitor(getRemapper())), varcreator(new VarCreation(getRemapper())), engine(
				new SearchEngine(new PCSolver(DEFAULTTHEORYID, getOptions(), monitor, varcreator, this, oneshot))){
}
Space::Space(Remapper* remapper, Translator* translator, const SolverOption& options, bool oneshot) :
		ExternalConstraintVisitor(remapper, translator, options, "Space"),
		monitor(new Monitor(getRemapper())), varcreator(new VarCreation(getRemapper())), engine(
				new SearchEngine(new PCSolver(DEFAULTTHEORYID, getOptions(), monitor, varcreator, this, oneshot))){
}
Space::~Space() {
	delete (engine);
	delete (monitor);
}

void Space::addMonitor(PropAndBackMonitor* m) {
	monitor->addMonitor(m);
}

void Space::finishParsing(){
  engine->finishParsing();
}

void Space::notifyUnsat(){
	engine->notifyUnsat();
}

bool Space::isCertainlyUnsat() const {
	return engine->isUnsat();
}

bool Space::isOptimizationProblem() const {
	return engine->isOptimizationProblem();
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
void Space::add(const MinimizeSubset& o){
	internalAdd(o, o.theoryid, *getEngine());
}
void Space::add(const OptimizeVar& o){
	internalAdd(o, o.theoryid, *getEngine());
}
void Space::add(const MinimizeAgg& o){
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
void Space::add(const CPBinaryRel& o){
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
void Space::add(const TwoValuedVarIdRequirement& o){
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

ModelExpand* Space::createModelExpand(Space* space, ModelExpandOptions options, const litlist& assumptions){
  space->getEngine()->addAssumptions(map(assumptions, *space->getRemapper()));
  if(space->isOptimizationProblem()){
    return new MinisatID::FindOptimalModels(space, options);
  }else{
    return new MinisatID::FindModels(space, options);
  }
}
