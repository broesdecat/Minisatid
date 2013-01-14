#include "external/OneShotTasks.hpp"
#include "external/Tasks.hpp"
#include "external/Space.hpp"
#include "external/ECNFPrinter.hpp"
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
	id2constr[disjunction.getID()] = new Disjunction(disjunction);
	marker2ids[newvar].push_back(disjunction.getID());
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
 * ts <=> Pnew | MF
 * P <=> ts & MT
 * Pnew <=> Agg
 * and MF assumed false, MT assumed true
 */
void OneShotUnsatCoreExtraction::add(const Aggregate& agg) {
	Aggregate extended(agg);
	auto oldhead = extended.head;
	auto newhead = getRemapper()->getNewVar();
	auto truemarker = getRemapper()->getNewVar();
	auto falsemarker = getRemapper()->getNewVar();
	auto tseitin = getRemapper()->getNewVar();
	extended.head = mkPosLit(newhead);
	switch (agg.sem) {
	case AggSem::DEF: {
		Rule impl(agg.getID(), tseitin, { mkPosLit(newhead), mkPosLit(falsemarker) }, false, agg.defID, agg.onlyif);
		Rule impl2(agg.getID(), var(oldhead), { mkPosLit(tseitin), mkPosLit(truemarker) }, true, agg.defID, agg.onlyif);
		space->add(impl);
		space->add(impl2);
		break;
	}
	case AggSem::COMP: {
		Implication impl(agg.getID(), mkPosLit(tseitin), ImplicationType::EQUIVALENT, { mkPosLit(newhead), mkPosLit(falsemarker) }, false);
		Implication impl2(agg.getID(), oldhead, ImplicationType::EQUIVALENT, { mkPosLit(tseitin), mkPosLit(truemarker) }, true);
		space->add(impl);
		space->add(impl2);
		break;
	}
	case AggSem::OR: {
		Implication impl2(agg.getID(), ~oldhead, ImplicationType::IMPLIES, { mkPosLit(newhead), mkPosLit(falsemarker) }, false);
		space->add(impl2);
		break;
	}
	}
	markerAssumptions.push_back(mkNegLit(falsemarker));
	markerAssumptions.push_back(mkPosLit(truemarker));
	id2constr[agg.getID()] = new Aggregate(agg);
	marker2ids[truemarker].push_back(agg.getID());
	marker2ids[falsemarker].push_back(agg.getID());
	space->add(extended);

}
/**
 * Exactly same idea is with the aggregate (but then defined)
 * From P <- Body
 * go to
 * 
 * ts <- Pnew | MF
 * P <- ts & MT
 * Pnew <- Body
 * and MF assumed false, MT assumed true
 */
void OneShotUnsatCoreExtraction::add(const Rule& rule) {
	Rule extended(rule);
	auto oldhead = extended.head;
	auto newhead = getRemapper()->getNewVar();
	auto truemarker = getRemapper()->getNewVar();
	auto falsemarker = getRemapper()->getNewVar();
	auto tseitin = getRemapper()->getNewVar();
	extended.head = newhead;
	Rule impl(rule.getID(), tseitin, { mkPosLit(newhead), mkPosLit(falsemarker) }, false, rule.definitionID, rule.onlyif);
	Rule impl2(rule.getID(), oldhead, { mkPosLit(tseitin), mkPosLit(truemarker) }, true, rule.definitionID, rule.onlyif);
	markerAssumptions.push_back(mkNegLit(falsemarker));
	markerAssumptions.push_back(mkPosLit(truemarker));
	id2constr[rule.getID()] = new Rule(rule);
	marker2ids[truemarker].push_back(rule.getID());
	marker2ids[falsemarker].push_back(rule.getID());
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
	mxopts = std::unique_ptr<ModelExpandOptions>(new ModelExpandOptions(0, Models::NONE, Models::NONE));
	mx = std::unique_ptr<ModelExpand>(new ModelExpand(space, *mxopts, { }));
	mx->setAssumptionsAsInternal(markerAssumptions);
	mx->execute();
	if (mx->isSat()) {
		return;
	}
	auto explanation = mx->getUnsatExplanation();
	//auto printer = RealECNFPrinter<std::ostream>(mx->getSpace(), clog, true);
	//clog << "Unsat core: \n";
	for (auto assumption : explanation) {
		for (auto id : marker2ids[var(assumption)]) {
			unsatcore.push_back(id);
            // TODO: do output this when running directly in MiniSAT
	//		clog << "\t";
	//		id2constr[id]->accept(&printer);
		}
	}
}

OneShotUnsatCoreExtraction::OneShotUnsatCoreExtraction(const SolverOption& options)
		: Task(options), ExternalConstraintVisitor(options, "unsat-core-extractor"), space(new Space(getRemapper(), getTranslator(), options, true)) {
}
OneShotUnsatCoreExtraction::~OneShotUnsatCoreExtraction() {
	for (auto pair : id2constr) {
		delete pair.second;
	}
	// delete space?
}
