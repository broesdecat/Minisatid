#include "OneShotTasks.hpp"
#include "Tasks.hpp"
#include "external/Space.hpp"
#include "theorysolvers/PCSolver.hpp"
#include "theorysolvers/InternalAdd.hpp"

using namespace std;
using namespace MinisatID;

template<>
void OneShotUnsatCoreExtraction::extAdd(const Disjunction& disjunction) {
	Disjunction extended(disjunction);
	auto newvar = space->getEngine()->newVar();
	extended.literals.push_back(mkPosLit(newvar));
	MAssert(id2Marker.find(maxid)==id2Marker.cend());
	id2Marker[maxid] = newvar;
	markerAssumptions.push_back(mkNegLit(newvar));
	add(extended, *space->getEngine());
}
// TODO other constraints
/*
 * Idee van bart: in plaats van de andere constraints aan te passen en te moeten zoeken naar waar en hoeveel markers er nodig zijn,
 * zorgen we enkel dat elke propagator als hij een explanation genereert, daar zijn marker literal aan toevoegt.
 * Voor bepaalde propagators kunnen we dat dan verder specialiseren, bvb definities.
 * => in getExplanation van PCSolver.
 * => so for each other constraint, give it a marker literal and the ids of its associated constraints (in propagatorfactory)
 */

void OneShotUnsatCoreExtraction::innerExecute() {
	ModelExpandOptions mxoptions(0, Models::NONE, Models::NONE);
	auto mx = ModelExpand(space, mxoptions, markerAssumptions);
	mx.execute();
	MAssert(mx.getSolutions().size()==0);
	// TODO  rest
}

OneShotUnsatCoreExtraction::OneShotUnsatCoreExtraction(const SolverOption& options) : Task(options), space(new Space(options, true)) {

}
OneShotUnsatCoreExtraction::~OneShotUnsatCoreExtraction() {
	delete (space);
}

OneShotMX::OneShotMX(SolverOption options, ModelExpandOptions mxoptions, const litlist& assumptions):
		Task(options),
	space(new Space(options, true)), mx(new ModelExpand(space, mxoptions, assumptions)){

}

OneShotMX::OneShotMX(Space* space, ModelExpandOptions mxoptions, const litlist& assumptions):
		Task(space->getOptions()),
	space(space), mx(new ModelExpand(space, mxoptions, assumptions)){

}

OneShotMX::~OneShotMX(){
	delete(space);
	delete(mx);
}

SearchEngine* OneShotMX::getEngine() { return space->getEngine(); }

void OneShotMX::innerExecute(){
	mx->execute();
}

bool OneShotMX::isSat() const {
	return mx->isSat();
}
bool OneShotMX::isUnsat() const {
	return mx->isUnsat();
}

void OneShotMX::notifySolvingAborted() {
	mx->notifySolvingAborted();
}
