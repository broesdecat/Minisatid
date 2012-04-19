#include "external/OneShotTasks.hpp"
#include "external/Tasks.hpp"
#include "external/Space.hpp"
#include "constraintvisitors/ECNFPrinter.hpp"
#include "space/SearchEngine.hpp"
#include "theorysolvers/PropagatorFactory.hpp"
#include "datastructures/InternalAdd.hpp"

using namespace std;
using namespace MinisatID;

template<>
void OneShotUnsatCoreExtraction::extAdd(const Disjunction& disjunction) {
	Disjunction extended(disjunction);
	auto newvar = space->getEngine()->newVar();
	extended.literals.push_back(mkPosLit(newvar));
	id2constr[maxid] = new Disjunction(disjunction);
	marker2ids[newvar].push_back(disjunction.id);
	markerAssumptions.push_back(mkNegLit(newvar));
	add(extended, *space->getEngine());
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
	auto mx = ModelExpand(space, mxoptions, markerAssumptions);
	mx.execute();
	MAssert(mx.getSolutions().size()==0);
	auto explan = mx.getUnsatExplanation();
	auto printer = RealECNFPrinter<std::ostream>(mx.getSpace(), clog);
	clog <<"Unsat core: \n";
	for(auto i=explan.cbegin(); i<explan.cend(); ++i){
		for(auto j=marker2ids[var(*i)].cbegin(); j<marker2ids[var(*i)].cend(); ++j){
			clog <<"\t";
			id2constr[*j]->accept(&printer);
		}
	}
	// TODO  rest
}

OneShotUnsatCoreExtraction::OneShotUnsatCoreExtraction(const SolverOption& options) : Task(options), space(new Space(options, true)) {

}
OneShotUnsatCoreExtraction::~OneShotUnsatCoreExtraction() {
}

OneShotMX::OneShotMX(SolverOption options, ModelExpandOptions mxoptions, const litlist& assumptions):
		MXTask(new Space(options, true)), localspace(true),
	mx(new ModelExpand(getSpace(), mxoptions, assumptions)){

}

OneShotMX::OneShotMX(Space* space, ModelExpandOptions mxoptions, const litlist& assumptions):
		MXTask(space), localspace(false),
	mx(new ModelExpand(space, mxoptions, assumptions)){

}

OneShotMX::~OneShotMX(){
	if(localspace){
		delete(getSpace());
	}
	delete(mx);
}

SearchEngine* OneShotMX::getEngine() const { return getSpace()->getEngine(); }

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
