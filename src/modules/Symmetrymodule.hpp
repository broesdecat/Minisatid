/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef SYMMMODULE_HPP_
#define SYMMMODULE_HPP_

#include "utils/Utils.hpp"
#include "theorysolvers/PCSolver.hpp"

#include <list>

namespace MinisatID {

class SymVars{
public:
	std::vector<std::vector<int> > symVars;
	std::set<unsigned int> forbiddenRows, forbiddenColumns;
	std::map<int, std::pair<unsigned int, unsigned int> > index;
	std::list<std::pair<int, unsigned int> > rowBacktrackLevels, columnBacktrackLevels;
	std::vector<std::set<int> > columns;


	// @pre: alle binnenste vectoren in args hebben zelfde lengte
	// @pre: alle Literals van args zijn positief
	SymVars(std::vector<std::vector<Lit> >& args){
		for(unsigned int i=0; i<args[0].size(); i++){
			columns.push_back(std::set<int>());
		}
		for(unsigned int i=0; i<args.size(); i++){
			std::vector<int> temp;
			for(unsigned int j=0; j<args[i].size(); j++){
				temp.push_back(var(args[i][j]));
				index.insert(std::pair<int, std::pair<unsigned int, unsigned int> >(var(args[i][j]), std::pair<unsigned int, unsigned int>(i,j)));
				columns[j].insert(var(args[i][j]));
			}
			symVars.push_back(temp);
		}
	}

	void print(){
		for(unsigned int i=0; i<symVars.size(); i++){
			for(unsigned int j=0; j<symVars[i].size() && !forbiddenRows.count(i); j++){
				if(!forbiddenColumns.count(j)){
					std::clog << symVars[i][j] << " | ";
				}else{
					std::clog << " | ";
				}
			}
			std::clog << "\n";
		}
		std::clog << "\n";
	}

	void propagate(const Lit& l, int level){
		std::map<int, std::pair<unsigned int,unsigned int> >::iterator index_it = index.find(var(l));
		if(index_it!=index.end()){ // present in table
			std::pair<unsigned int,unsigned int> coords = index_it->second;
			unsigned int row=coords.first; unsigned int column = coords.second;
			if(!forbiddenRows.count(row) && !forbiddenColumns.count(column)){
				forbiddenRows.insert(row);
				rowBacktrackLevels.push_back(std::pair<int, unsigned int>(level,row));
			}
		}
	}

	template<class Solver>
	void backtrack(int level, const Lit& l, Solver solver){
		while(!rowBacktrackLevels.empty() && level < rowBacktrackLevels.back().first){
			forbiddenRows.erase(rowBacktrackLevels.back().second);
			rowBacktrackLevels.pop_back();
		}
		while(!columnBacktrackLevels.empty() && level < columnBacktrackLevels.back().first){
			forbiddenColumns.erase(columnBacktrackLevels.back().second);
			columnBacktrackLevels.pop_back();
		}

		int variable = var(l);
		std::map<int, std::pair<unsigned int,unsigned int> >::iterator index_it = index.find(variable);
		if(index_it!=index.end()){ // present in table
			std::pair<unsigned int,unsigned int> coords = index_it->second;
			unsigned int row=coords.first; unsigned int column = coords.second;
			if(!forbiddenRows.count(row) && !forbiddenColumns.count(column)){
				forbiddenColumns.insert(column);
				columnBacktrackLevels.push_back(std::pair<int, unsigned int>(level,column));// is level juist?
				for(unsigned int i=0; i<symVars.size(); i++){
					if(!forbiddenRows.count(i)){
						Lit symLit = mkLit(symVars[i][column],!sign(l));
						if(solver->value(symLit)==l_Undef){
							solver->setTrue(symLit, NULL);
						}else{
							if(sign(l)){
								assert(solver->value(symLit)==l_True);
							}else{
								assert(solver->value(symLit)==l_False);
							}
						}
					}
				}
			}
		}
	}

	bool isPropagated(const Lit& conflict) const{
		bool result = false;
		for(std::set<unsigned int>::const_iterator sui_it=forbiddenColumns.begin(); !result && sui_it!=forbiddenColumns.end(); sui_it++){
			result=columns[*sui_it].count(var(conflict));
		}
		return result;
	}
};

template<class Solver>
class SymmetryPropagator {
private:
	Solver solver;
	std::vector<std::vector<std::vector<Lit> > > symmgroups;

	std::vector<SymVars*> symClasses;

	bool parsing;

public:
	SymmetryPropagator(Solver s) : solver(s), parsing(true){}
	virtual ~SymmetryPropagator() {
		deleteList<SymVars>(symClasses);
	}

	// DPLL-T methods

	void add(const std::vector<std::vector<Lit> >& symmgroup){
		assert(parsing);
		symmgroups.push_back(symmgroup);
	}

	bool analyze(const Lit& p){
		bool propagatedBySymClasses = false;
        for(auto i=symClasses.begin(); !propagatedBySymClasses && i<symClasses.end(); i++){
        	propagatedBySymClasses = (*i)->isPropagated(p);
        }
        return propagatedBySymClasses;
	}

	void finishParsing() {
	    for(auto i=symmgroups.begin(); i<symmgroups.end(); ++i){
	    	symClasses.push_back(new SymVars(*i));
	    }
	}

	void propagate(const Lit& l) {
	   	for(auto vs_it=symClasses.begin(); vs_it!=symClasses.end(); vs_it++){
			(*vs_it)->propagate(l,solver->getCurrentDecisionLevel());
		}
	}

	void backtrackDecisionLevels(int level, const Lit& decision) {
        for(auto vs_it=symClasses.begin(); vs_it!=symClasses.end(); ++vs_it){
        	(*vs_it)->backtrack(level, decision, solver);
		}
	}
};

}

#endif /* SYMMMODULE_HPP_ */
