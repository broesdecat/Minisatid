#include "external/OneShotTasks.hpp"
#include "external/Tasks.hpp"
#include "external/Space.hpp"
#include "constraintvisitors/ECNFPrinter.hpp"
#include "space/Remapper.hpp"
#include "space/SearchEngine.hpp"
#include "theorysolvers/PropagatorFactory.hpp"
#include "datastructures/InternalAdd.hpp"

using namespace std;
using namespace MinisatID;

void OneShotUnsatCoreExtraction::add(const Disjunction& disjunction) {
	Disjunction extended(disjunction);
	auto newvar = getRemapper()->getNewVar();
	extended.literals.push_back(mkPosLit(newvar));
	id2constr[disjunction.id] = new Disjunction(disjunction);
	marker2ids[newvar].push_back(disjunction.id);
	markerAssumptions.push_back(mkNegLit(newvar));
	space->add(extended);
}
void OneShotUnsatCoreExtraction::add(const WLSet& set) {
	space->add(set);
}
/**
 * From P <=> Agg
 * go to
 *
 * P <=> (Pnew | M1) & M2
 * Pnew <=> Agg
 * and M1 assumed false, M2 assumed true
 */
void OneShotUnsatCoreExtraction::add(const Aggregate& agg) {
	Aggregate extended(agg);
	auto oldhead = extended.head;
	auto newhead = getRemapper()->getNewVar();
	auto truemarker = getRemapper()->getNewVar();
	auto falsemarker = getRemapper()->getNewVar();
	auto tseitin = getRemapper()->getNewVar();
	extended.head = mkPosLit(newhead);
	switch(agg.sem){
	case AggSem::DEF:{
		Rule impl(tseitin, { mkPosLit(newhead), mkPosLit(falsemarker) }, false, agg.defID);
		Rule impl2(var(oldhead), { mkPosLit(tseitin), mkPosLit(truemarker) }, true, agg.defID);
		space->add(impl);
		space->add(impl2);
		break;}
	case AggSem::COMP:{
		Implication impl(mkPosLit(tseitin), ImplicationType::EQUIVALENT, { mkPosLit(newhead), mkPosLit(falsemarker) }, false);
		Implication impl2(oldhead, ImplicationType::EQUIVALENT, { mkPosLit(tseitin), mkPosLit(truemarker) }, true);
		space->add(impl);
		space->add(impl2);
		break;}
	case AggSem::OR:{
		Implication impl2(~oldhead, ImplicationType::IMPLIES, { mkPosLit(newhead), mkPosLit(falsemarker) }, false);
		space->add(impl2);
		break;}
	}
	markerAssumptions.push_back(mkNegLit(falsemarker));
	markerAssumptions.push_back(mkPosLit(truemarker));
	id2constr[agg.id] = new Aggregate(agg);
	marker2ids[truemarker].push_back(agg.id);
	marker2ids[falsemarker].push_back(agg.id);
	space->add(extended);

}
/**
 * Exactly same idea is with the aggregate (but then defined
 */
void OneShotUnsatCoreExtraction::add(const Rule& rule) {
	Rule extended(rule);
	auto oldhead = extended.head;
	auto newhead = getRemapper()->getNewVar();
	auto truemarker = getRemapper()->getNewVar();
	auto falsemarker = getRemapper()->getNewVar();
	auto tseitin = getRemapper()->getNewVar();
	extended.head = newhead;
	Rule impl(tseitin, { mkPosLit(newhead), mkPosLit(falsemarker) }, false, rule.definitionID);
	Rule impl2(oldhead, { mkPosLit(tseitin), mkPosLit(truemarker) }, true, rule.definitionID);
	markerAssumptions.push_back(mkNegLit(falsemarker));
	markerAssumptions.push_back(mkPosLit(truemarker));
	id2constr[rule.id] = new Rule(rule);
	marker2ids[truemarker].push_back(rule.id);
	marker2ids[falsemarker].push_back(rule.id);
	space->add(extended);
	space->add(impl);
	space->add(impl2);
}
// TODO other constraints:
/*
 * Idee van bart: in plaats van de andere constraints aan te passen en te moeten zoeken naar waar en hoeveel markers er nodig zijn,
 * zorgen we enkel dat elke propagator als hij een explanation genereert, daar zijn marker literal aan toevoegt.
 * Voor bepaalde propagators kunnen we dat dan verder specialiseren, bvb definities.
 * => in getExplanation van PCSolver.
 * => so for each other constraint, give it a marker literal and the ids of its associated constraints (in propagatorfactory)
 *
 * SO: handle by overwriting add and createclause methods, so that they can take a marker literal if applicable
 */

void OneShotUnsatCoreExtraction::innerExecute() {
	ModelExpandOptions mxoptions(0, Models::NONE, Models::NONE);
	auto mx = ModelExpand(space, mxoptions, { });
	mx.setAssumptionsAsInternal(markerAssumptions);
	mx.execute();
	MAssert(mx.isUnsat());
	auto explan = mx.getUnsatExplanation();
	auto printer = RealECNFPrinter<std::ostream>(mx.getSpace(), clog, true);
	clog << "Unsat core: \n";
	for (auto i = explan.cbegin(); i < explan.cend(); ++i) {
		for (auto j = marker2ids[var(*i)].cbegin(); j < marker2ids[var(*i)].cend(); ++j) {
			unsatcore.push_back(*j);
			clog << "\t";
			id2constr[*j]->accept(&printer);
		}
	}
	// TODO minimization?
	// TODO translation into some useful format
}

OneShotUnsatCoreExtraction::OneShotUnsatCoreExtraction(const SolverOption& options) :
		Task(options), ExternalConstraintVisitor(options, "unsat-core-extractor"), space(new Space(getRemapper(), getTranslator(), options, true)) {
}
OneShotUnsatCoreExtraction::~OneShotUnsatCoreExtraction() {
	// delete space?
}
