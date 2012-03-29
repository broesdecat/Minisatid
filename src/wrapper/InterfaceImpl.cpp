/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#include "wrapper/InterfaceImpl.hpp"

#include <cstdlib>
#include <vector>
#include <algorithm>
#include <limits>

#include "utils/ResourceManager.hpp"
#include "utils/Print.hpp"
#include "external/Translator.hpp"
#include "external/SearchMonitor.hpp"
#include "theorysolvers/PCSolver.hpp"

using namespace std;
using namespace MinisatID;
//
//// NOTE: called by global operator<<(const Lit& l)!
//void WrappedSolver::printLiteral(std::ostream& output, const Lit& l) const{
//	if(canBackMapLiteral(l) && hasprintcallback){
//		output << printliteral(getRemapper()->getLiteral(l).getValue());
//	}else if(canBackMapLiteral(l)){
//		if(hasSolMonitor()){
//			getSolMonitor().printLiteral(output, getRemapper()->getLiteral(l));
//		}else{
//			auto lit = getRemapper()->getLiteral(l);
//			output <<(lit.hasSign()?"~":"") <<"tseitin_" <<abs(lit.getValue());
//		}
//	}else{
//		output <<(sign(l)?"-":"") <<"intern_" <<var(l)+1; // NOTE: do not call <<l, this will cause an infinite loop (as that calls this method!)
//	}
//}
//
//void WrappedSolver::printCurrentOptimum(const Weight& value) const{
//	getSolMonitor().notifyCurrentOptimum(value);
//}
//
//SATVAL WrappedSolver::finishParsing(){
//	if(hasSolMonitor()){
//		getSolMonitor().notifyStartDataInit();
//		printInitDataStart(verbosity());
//	}
//
//	getSolver()->finishParsing();
//	if(getSolver()->isUnsat()){
//		if(hasSolMonitor()){
//			getSolMonitor().notifyUnsat();
//		}
//	}
//	state = PARSED;
//
//	if(hasSolMonitor()){
//		getSolMonitor().notifyEndDataInit();
//		printInitDataEnd(verbosity(), getSolMonitor().isUnsat());
//	}
//
//	return getSolver()->isUnsat()?SATVAL::UNSAT:SATVAL::POS_SAT;
//}
//
///*
// * Solution options:
// * 		PRINT_NONE: never print any models
// * 		PRINT_BEST: after solving an optimization problem, only print the optimum model or the best model when notifyTimeout is called
// * 			when not an optimization problem, comes down to print all
// * 		PRINT_ALL: print every model when adding it to the solution
// *
// * 		MODELEXAND: search for a solution
// * 		PROPAGATE: only do unit propagation (and print nothing, not even when a model is found)
// */
//void WrappedSolver::solve(){
//	if(solutionmonitor==NULL){
//		throw idpexception("Solving without instantiating any solution monitor.\n");
//	}
//
//	if(!getSolMonitor().isUnsat() && state==INIT){
//		if(finishParsing()==SATVAL::UNSAT){
//			getSolMonitor().notifyUnsat();
//		}
//	}
//
//	if(!getSolMonitor().isUnsat()){
//		assert(state==PARSED);
//
//		getSolMonitor().notifyStartSolving();
//		printSolveStart(verbosity());
//
//		litlist assumptions;
//		checkLits(getSolMonitor().getAssumptions(), assumptions);
//
//		if(!getSolver()->solve(assumptions, getSolMonitor().getOptions())){
//			getSolMonitor().notifyUnsat();
//		}
//
//		if(getSolMonitor().getInferenceOption()==Inference::MODELEXPAND){
//			state = SOLVED;
//		}
//
//		getSolMonitor().notifyEndSolving();
//	}
//
//	getSolMonitor().notifySolvingFinished();
//}
//
//void WrappedSolver::addModel(const InnerModel& model){
//	Model* outmodel = new Model();
//	outmodel->literalinterpretations = getBackMappedModel(model.litassignments);
//	outmodel->variableassignments = model.varassignments;
//	getSolMonitor().addModel(outmodel);
//}
//
//void WrappedSolver::notifyOptimalModelFound(){
//	assert(hasOptimization());
//	getSolMonitor().notifyOptimalModelFound();
//}
//
//bool WrappedSolver::canBackMapLiteral(const Lit& lit) const{
//	return getRemapper()->wasInput(var(lit));
//}
//
//Literal WrappedSolver::getBackMappedLiteral(const Lit& lit) const{
//	assert(canBackMapLiteral(lit));
//	return getRemapper()->getLiteral(lit);
//}
//
////Translate into original vocabulary
//vector<Literal> WrappedSolver::getBackMappedModel(const std::vector<Lit>& model) const{
//	vector<Literal> outmodel;
//	for(auto i=model.cbegin(); i!=model.cend(); ++i){
//		if(canBackMapLiteral(*i)){
//			outmodel.push_back(getBackMappedLiteral(*i));
//		}
//	}
//	sort(outmodel.begin(), outmodel.end());
//	return outmodel;
//}
//
//SATVAL WrappedSolver::getSatState() const{ // FIXME check consistency with solmonitor
//	return getSolver()->satState();
//}
//
//void WrappedSolver::addMonitor(SearchMonitor * const mon){
//	monitors.push_back(mon);
//	getSolver()->requestMonitor(this);
//}
//
//template<>
//void WrappedSolver::notifyMonitor(const InnerPropagation& obj){
//	if(canBackMapLiteral(obj.propagation)){
//		Literal lit = getBackMappedLiteral(obj.propagation);
//		for(auto i=monitors.cbegin(); i<monitors.cend(); ++i){
//			(*i)->notifyPropagated(lit, obj.decisionlevel);
//		}
//	}
//}
//
//template<>
//void WrappedSolver::notifyMonitor(const InnerBacktrack& obj){
//	for(auto i=monitors.cbegin(); i<monitors.cend(); ++i){
//		(*i)->notifyBacktracked(obj.untillevel);
//	}
//}
