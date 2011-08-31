/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#include "external/ExternalInterface.hpp"
#include "wrapper/InterfaceImpl.hpp"
#include "external/SearchMonitor.hpp"
#include "external/Translator.hpp"

#include "external/LazyClauseSupport.hpp"

using namespace std;
using namespace MinisatID;

WrappedLogicSolver::WrappedLogicSolver(){}

WrappedLogicSolver::~WrappedLogicSolver(){
}

bool WrappedLogicSolver::hasOptimization() const {
	return getImpl()->hasOptimization();
}

void WrappedLogicSolver::printStatistics() const {
	getImpl()->printStatistics();
}

void WrappedLogicSolver::solve(Solution* sol){
	getImpl()->setSolutionMonitor(sol);
	getImpl()->solve();
}

void WrappedLogicSolver::addMonitor(SearchMonitor* const monitor){
	getImpl()->addMonitor(monitor);
}



WrappedPCSolver::WrappedPCSolver(const SolverOption& modes)
		:WrappedLogicSolver(), impl(new PCWrapperPimpl(modes)){
}

WrappedPCSolver::~WrappedPCSolver(){
	delete impl;
}

WrapperPimpl* WrappedPCSolver::getImpl() const {
	return impl;
}

PCWrapperPimpl* WrappedPCSolver::getPCImpl() const {
	return impl;
}

template<class T>
bool WrappedPCSolver::add(const T& sentence){
	return getPCImpl()->add<T>(sentence);
}

WrappedSOSolver::WrappedSOSolver(const SolverOption& modes):
		WrappedLogicSolver(), impl(new SOWrapperPimpl(modes)){
}

WrappedSOSolver::~WrappedSOSolver(){
	delete impl;
}

WrapperPimpl* WrappedSOSolver::getImpl() const {
	return impl;
}

SOWrapperPimpl* WrappedSOSolver::getSOImpl() const {
	return impl;
}

template<class T>
bool WrappedSOSolver::add(int modalid, const T& sentence){
	return getSOImpl()->add(modalid, sentence);
}

// Only those explicitly instantiated (here or elsewhere) will be available in a compiled library
template bool WrappedPCSolver::add(const Disjunction& sentence);
template bool WrappedPCSolver::add(const DisjunctionRef& sentence);
template bool WrappedPCSolver::add(const Equivalence& sentence);
template bool WrappedPCSolver::add(const Rule& sentence);
template bool WrappedPCSolver::add(const Set& sentence);
template bool WrappedPCSolver::add(const WSet& sentence);
template bool WrappedPCSolver::add(const WLSet& sentence);
template bool WrappedPCSolver::add(const Aggregate& sentence);
template bool WrappedPCSolver::add(const MinimizeSubset& sentence);
template bool WrappedPCSolver::add(const MinimizeOrderedList& sentence);
template bool WrappedPCSolver::add(const MinimizeVar& sentence);
template bool WrappedPCSolver::add(const CPIntVarRange& sentence);
template bool WrappedPCSolver::add(const CPIntVarEnum& sentence);
template bool WrappedPCSolver::add(const CPBinaryRel& sentence);
template bool WrappedPCSolver::add(const CPBinaryRelVar& sentence);
template bool WrappedPCSolver::add(const CPSumWeighted& sentence);
template bool WrappedPCSolver::add(const CPCount& sentence);
template bool WrappedPCSolver::add(const CPAllDiff& sentence);
template bool WrappedPCSolver::add(const ForcedChoices& sentence);
template bool WrappedPCSolver::add(const SymmetryLiterals& sentence);
template bool WrappedPCSolver::add(const Symmetry& sentence);
template bool WrappedPCSolver::add(const LazyClause& sentence);

template bool WrappedSOSolver::add(int modalid, const Disjunction& sentence);
template bool WrappedSOSolver::add(int modalid, const DisjunctionRef& sentence);
template bool WrappedSOSolver::add(int modalid, const Rule& sentence);
template bool WrappedSOSolver::add(int modalid, const Set& sentence);
template bool WrappedSOSolver::add(int modalid, const WSet& sentence);
template bool WrappedSOSolver::add(int modalid, const WLSet& sentence);
template bool WrappedSOSolver::add(int modalid, const Aggregate& sentence);
template bool WrappedSOSolver::add(int modalid, const RigidAtoms& sentence);
template bool WrappedSOSolver::add(int modalid, const SubTheory& sentence);
