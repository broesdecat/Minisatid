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
#include "external/MonitorInterface.hpp"
#include "external/Translator.hpp"

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

void WrappedLogicSolver::addMonitor(Monitor* const monitor){
	getImpl()->addMonitor(monitor);
}



WrappedPCSolver::WrappedPCSolver(const SolverOption& modes)
		:WrappedLogicSolver(), impl(new ExternalPCImpl(modes)){
}

WrappedPCSolver::~WrappedPCSolver(){
	delete impl;
}

WLSImpl* WrappedPCSolver::getImpl() const {
	return impl;
}

ExternalPCImpl* WrappedPCSolver::getPCImpl() const {
	return impl;
}

template<class T>
bool WrappedPCSolver::add(const T& sentence){
	return getPCImpl()->add<T>(sentence);
}


WrappedSOSolver::WrappedSOSolver(const SolverOption& modes):
		WrappedLogicSolver(), impl(new WSOLSImpl(modes)){
}

WrappedSOSolver::~WrappedSOSolver(){
	delete impl;
}

WLSImpl* WrappedSOSolver::getImpl() const {
	return impl;
}

WSOLSImpl* WrappedSOSolver::getSOImpl() const {
	return impl;
}

bool WrappedSOSolver::add(int modalid, const Disjunction& sentence){
	return getSOImpl()->add(modalid, sentence);
}
bool WrappedSOSolver::add(int modalid, const DisjunctionRef& sentence){
	return getSOImpl()->add(modalid, sentence);
}
bool WrappedSOSolver::add(int modalid, const Rule& sentence){
	return getSOImpl()->add(modalid, sentence);
}
bool WrappedSOSolver::add(int modalid, const Set& sentence){
	return getSOImpl()->add(modalid, sentence);
}
bool WrappedSOSolver::add(int modalid, const WSet& sentence){
	return getSOImpl()->add(modalid, sentence);
}
bool WrappedSOSolver::add(int modalid, const WLSet& sentence){
	return getSOImpl()->add(modalid, sentence);
}
bool WrappedSOSolver::add(int modalid, const Aggregate& sentence){
	return getSOImpl()->add(modalid, sentence);
}
bool WrappedSOSolver::add(int modalid, const RigidAtoms& sentence){
	return getSOImpl()->add(modalid, sentence);
}
bool WrappedSOSolver::add(int modalid, const SubTheory& sentence){
	return getSOImpl()->add(modalid, sentence);
}
