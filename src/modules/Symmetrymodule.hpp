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
#include "utils/Print.hpp"

#include <list>

namespace MinisatID {

typedef std::pair<unsigned int, unsigned int> uintpair;

class SymVars{
public:
	std::vector<std::vector<Var> > symVars;
	std::map<Var,  uintpair> activeVars;
	std::set<Lit> propagatedLits;
	std::set<unsigned int> allowedColumns;
	std::set<unsigned int> allowedRows;
	std::list<std::pair<int, unsigned int> > columnBacktrackLevels;
	std::list<std::pair<int, std::pair<unsigned int,std::vector<Lit> > > > rowBacktrackLevels;


	// @pre: alle binnenste vectoren in args hebben zelfde lengte
	// @pre: alle Literals van args zijn positief
	SymVars(std::vector<std::vector<Lit> >& args){
		for(unsigned int i=0; i<args.size(); ++i){
			for(unsigned int j=0; j<args[i].size(); ++j){
				activeVars.insert(std::pair<Var, uintpair >(var(args[i][j]), uintpair(j,i)));
				allowedRows.insert(j);
				if(symVars.size()<=j){
					symVars.push_back(std::vector<Var>());
				}
				symVars[j].push_back(var(args[i][j]));
			}
			allowedColumns.insert(i);
		}
	}

	void print(){
		for(auto rows_it=allowedRows.cbegin(); rows_it!=allowedRows.cend(); ++rows_it){
			for(auto columns_it=allowedColumns.cbegin(); columns_it!=allowedColumns.cend(); ++columns_it){
				std::clog << symVars[*rows_it][*columns_it]+1 << " | ";
			}
			std::clog << "\n";
		}
		std::clog << "\n";
	}

	template<class Solver>
	bool propagate(const Lit& l, int level, Solver& solver){
		bool conflict=false;
		auto var_it = activeVars.find(var(l));
		if(var_it!=activeVars.cend()){ // present in table, so row and column are still allowed
			unsigned int row=var_it->second.first;
			unsigned int column = var_it->second.second;
			std::vector<Lit> propLits;
			for(auto columns_it=allowedColumns.cbegin(); columns_it!=allowedColumns.cend(); ++columns_it){
				Var symVar = symVars[row][*columns_it];
				activeVars.erase(symVar);
				if(*columns_it!=column){
					Lit symLit = mkLit(symVar,sign(l));
					if(solver.value(symLit)==l_Undef){
						solver.setTrue(symLit, NULL);
						propagatedLits.insert(symLit);
						propLits.push_back(symLit);
					}else{
						if(sign(symLit)){
							conflict=solver.value(symLit)==l_False;
						}else{
							conflict=solver.value(symLit)==l_True;
						}
					}
				}
			}
			allowedRows.erase(row);
			auto entry = std::pair<unsigned int,std::vector<Lit> >(row,propLits);
			rowBacktrackLevels.push_back(std::pair<int, std::pair<unsigned int,std::vector<Lit> > >(level,entry));
		}
		return conflict;
	}

	void backtrack(int level, const Lit& l){
		while(!columnBacktrackLevels.empty() && level < columnBacktrackLevels.back().first){
			unsigned int column = columnBacktrackLevels.back().second;
			for(auto rows_it=allowedRows.cbegin(); rows_it!=allowedRows.cend(); ++rows_it){
				activeVars[symVars[*rows_it][column]]=std::pair<unsigned int,unsigned int>(*rows_it,column);
			}
			allowedColumns.insert(column);
			columnBacktrackLevels.pop_back();
		}
		while(!rowBacktrackLevels.empty() && level < rowBacktrackLevels.back().first){
			unsigned int row = rowBacktrackLevels.back().second.first;
			for(auto columns_it=allowedColumns.cbegin(); columns_it!=allowedColumns.cend(); ++columns_it){
				activeVars[symVars[row][*columns_it]]=std::pair<unsigned int,unsigned int>(row,*columns_it);
			}
			std::vector<Lit> propLits=rowBacktrackLevels.back().second.second;
			for(auto lits_it=propLits.cbegin(); lits_it!=propLits.cend(); ++lits_it){
				propagatedLits.erase(*lits_it);
			}
			allowedRows.insert(row);
			rowBacktrackLevels.pop_back();
		}
		auto var_it = activeVars.find(var(l));
		if(var_it!=activeVars.cend()){
			unsigned int column = var_it->second.second;
			for(auto rows_it=allowedRows.cbegin(); rows_it!=allowedRows.cend(); ++rows_it){
				activeVars.erase(symVars[*rows_it][column]);
			}
			allowedColumns.erase(column);
			columnBacktrackLevels.push_back(std::pair<int, unsigned int>(level,column));
		}
	}

	bool isPropagated(const Lit& conflictLit) const{
		return propagatedLits.count(conflictLit);
	}
};

template<class Solver>
class SymmetryPropagator: public Propagator{
private:
	std::vector<std::vector<std::vector<Lit> > > symmgroups;
	bool generatedConflict;

	std::vector<SymVars*> symClasses;

	bool parsing;

public:
	SymmetryPropagator(Solver s) :
			Propagator(s), parsing(true),
			adding(false){
		getPCSolver().accept(this, EV_BACKTRACK);
		getPCSolver().accept(this, EV_ADDCLAUSE);
		getPCSolver().accept(this, EV_SYMMETRYANALYZE);
		getPCSolver().accept(this, EV_SYMMCHECK1);
		getPCSolver().accept(this, EV_SYMMCHECK2);
		getPCSolver().acceptFinishParsing(this, false);
	}

	virtual ~SymmetryPropagator() {
		deleteList<SymVars>(symClasses);
	}

	// DPLL-T methods

	void add(const std::vector<std::vector<Lit> >& symmgroup){
		assert(parsing);
		symmgroups.push_back(symmgroup);
	}

	virtual const char* getName			() const { return "symmetry"; }
	virtual int		getNbOfFormulas		() const { return 0; }

	bool symmetryPropagationOnAnalyze(const Lit& p){
		bool propagatedBySymClasses = false;
        for(auto i=symClasses.cbegin(); !propagatedBySymClasses && i<symClasses.cend(); i++){
        	propagatedBySymClasses = (*i)->isPropagated(p);
        }
        return propagatedBySymClasses;
	}

	void finishParsing(bool& present, bool& unsat) {
		parsing = false;
	    for(auto i=symmgroups.begin(); i<symmgroups.end(); ++i){
	    	symClasses.push_back(new SymVars(*i));
	    }
	    if(symmgroups.size()==0 && symmetries.size()==0){
	    	present = false;
	    }
	}

	bool checkSymmetryAlgo1(const Lit& l) {
	   	for(auto vs_it=symClasses.cbegin(); vs_it!=symClasses.cend(); vs_it++){
			(*vs_it)->propagate(l,getPCSolver().getCurrentDecisionLevel(), getPCSolver());
		}
	   	return generatedConflict;
	}

	void notifyBacktrack(int untillevel, const Lit& decision) {
		generatedConflict=false;
        for(auto vs_it=symClasses.cbegin(); vs_it!=symClasses.cend(); ++vs_it){
        	(*vs_it)->backtrack(untillevel, decision);
		}
	}

	// Different symmetry strategy, TODO should be split into different classes
	// => if a clause is added, add all symmetric clauses also
	// => when a clause is deleted, all symmetric ones have to be deleted too!
	// => INVARIANT: for any clause in the db, all its symmetric ones are always also in the db
		// FIXME will not compile with other sat solvers
private:
	std::vector<std::vector<Lit> > addedClauses;
	std::map<Var, std::vector<uint> > var2symmetries;
	std::vector<std::map<Var, Var> > symmetries;
	bool adding;

    bool addSymmetricClause(const std::vector<Lit>& clause, const std::map<Var, Var>& symmetry){
		InnerDisjunction newclause;
		litlist& lits = newclause.literals;
		bool allfalse = true;
		int level = 0;
		for (vsize i = 0; i < clause.size(); ++i) {
			auto it = symmetry.find(var(clause[i]));
			if (it == symmetry.cend()) {
				lits.push_back(clause[i]);
			} else {
				lits.push_back(mkLit((*it).second, sign(clause[i])));
			}

			if (allfalse && getPCSolver().value(lits.back()) == l_False) {
				int varlevel = getPCSolver().getLevel(var(lits.back()));
				if (varlevel - 1 > level) {
					level = varlevel - 1;
				}
			} else {
				allfalse = false;
			}
		}

		if (allfalse) {
			if (level == 0) {
				return false;
			}
			getPCSolver().backtrackTo(level);
		}
		rClause rc = getPCSolver().createClause(newclause, true);
		getPCSolver().addLearnedClause(rc);
		return true;
    }

    bool addSymmetricClauses(std::vector<Lit> clause) {
		bool noConflict = true;
		//add all symmetries
		std::set<uint> symmindices;
		for (vsize i = 0; i < clause.size(); ++i) {
			auto it = var2symmetries.find(var(clause[i]));
			if (it == var2symmetries.cend()) {
				continue;
			}
			symmindices.insert((*it).second.cbegin(), (*it).second.cend());
		}
		if (symmindices.size() > 0) {
			for (auto index = symmindices.cbegin(); noConflict && index != symmindices.cend(); ++index) {
				noConflict = addSymmetricClause(clause, symmetries.at(*index));
			}
		}
		return noConflict;
	}

public:
	void add(const std::map<Var, Var>& symmetry){
		assert(parsing);
		symmetries.push_back(symmetry);
		for(auto i=symmetry.cbegin(); i!=symmetry.cend(); ++i){
			var2symmetries[(*i).first].push_back(symmetries.size()-1);
		}
	}

	void notifyClauseAdded(rClause clauseID){
		if(parsing){
			return;
		}
		if(adding){
			return;
		}
		std::vector<Lit> clause;
		for(int i=0; i<getPCSolver().getClauseSize(clauseID); ++i){
			clause.push_back(getPCSolver().getClauseLit(clauseID, i));
		}
		addedClauses.push_back(clause);
	}

    bool checkSymmetryAlgo2() {
		bool noConflict = true;
		adding = true;
		if (addedClauses.size() > 0) {
			for (auto it = addedClauses.cbegin(); noConflict && it != addedClauses.cend(); ++it) {
				noConflict = addSymmetricClauses(*it);
			}
		}
		addedClauses.clear();
		adding = false;
		return noConflict;
	}
};
}

#endif /* SYMMMODULE_HPP_ */
