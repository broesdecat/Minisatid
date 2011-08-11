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

namespace MinisatID {

class SymVars{
public:
	std::vector<std::vector<Var> > symVars;
	std::map<Var, std::pair<unsigned int, unsigned int> > activeVars;
	std::set<Lit> propagatedLits;
	std::set<unsigned int> allowedColumns;
	std::set<unsigned int> allowedRows;
	std::list<std::pair<int, unsigned int> > columnBacktrackLevels;
	std::list<std::pair<int, std::pair<unsigned int,std::vector<Lit> > > > rowBacktrackLevels;


	// @pre: alle binnenste vectoren in args hebben zelfde lengte
	// @pre: alle Literals van args zijn positief
	// TODO: input zuigt, zou moeten var zijn ipv lit, en zou moeten getransponeerd zijn
	SymVars(std::vector<std::vector<Lit> >& args){
		for(unsigned int i=0; i<args.size(); ++i){
			for(unsigned int j=0; j<args[i].size(); ++j){
				activeVars.insert(std::pair<Var, std::pair<unsigned int, unsigned int> >(var(args[i][j]), std::pair<unsigned int, unsigned int>(j,i)));
				allowedRows.insert(j);
				if(symVars.size()<=j){
					symVars.push_back(std::vector<Var>());
				}
				symVars[j].push_back(var(args[i][j]));
			}
			allowedColumns.insert(i);
		}
//		print();
	}

	void print(){
		for(auto rows_it=allowedRows.begin(); rows_it!=allowedRows.end(); ++rows_it){
			for(auto columns_it=allowedColumns.begin(); columns_it!=allowedColumns.end(); ++columns_it){
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
		if(var_it!=activeVars.end()){ // present in table, so row and column are still allowed
			unsigned int row=var_it->second.first;
			unsigned int column = var_it->second.second;
			std::vector<Lit> propLits;
			for(auto columns_it=allowedColumns.begin(); columns_it!=allowedColumns.end(); ++columns_it){
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
//			for(auto lits_it=propLits.begin(); lits_it!=propLits.end(); ++lits_it){
//				std::clog << "proplits: " << *lits_it << "\n";
//			}
			allowedRows.erase(row);
			std::pair<unsigned int,std::vector<Lit> > entry = std::pair<unsigned int,std::vector<Lit> >(row,propLits);
			rowBacktrackLevels.push_back(std::pair<int, std::pair<unsigned int,std::vector<Lit> > >(level,entry));
		}
		return conflict;
	}

	void backtrack(int level, const Lit& l){
//		std::clog << level << " | " << l << "\n";
//		print();
		while(!columnBacktrackLevels.empty() && level < columnBacktrackLevels.back().first){
			unsigned int column = columnBacktrackLevels.back().second;
			for(auto rows_it=allowedRows.begin(); rows_it!=allowedRows.end(); ++rows_it){
				activeVars[symVars[*rows_it][column]]=std::pair<unsigned int,unsigned int>(*rows_it,column);
			}
			allowedColumns.insert(column);
			columnBacktrackLevels.pop_back();
		}
		while(!rowBacktrackLevels.empty() && level < rowBacktrackLevels.back().first){
			unsigned int row = rowBacktrackLevels.back().second.first;
			for(auto columns_it=allowedColumns.begin(); columns_it!=allowedColumns.end(); ++columns_it){
				activeVars[symVars[row][*columns_it]]=std::pair<unsigned int,unsigned int>(row,*columns_it);
			}
			std::vector<Lit> propLits=rowBacktrackLevels.back().second.second;
			for(auto lits_it=propLits.begin(); lits_it!=propLits.end(); ++lits_it){
				propagatedLits.erase(*lits_it);
			}
			allowedRows.insert(row);
			rowBacktrackLevels.pop_back();
		}
		auto var_it = activeVars.find(var(l));
		if(var_it!=activeVars.end()){
			unsigned int column = var_it->second.second;
			for(auto rows_it=allowedRows.begin(); rows_it!=allowedRows.end(); ++rows_it){
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
		getPCSolver().acceptFinishParsing(this, false);
	}

	virtual ~SymmetryPropagator() {
		deleteList<SymVars>(symClasses);
	}

	bool hasGeneratedConflict(){
		return generatedConflict;
	}

	// DPLL-T methods

	void add(const std::vector<std::vector<Lit> >& symmgroup){
		assert(parsing);
		symmgroups.push_back(symmgroup);
	}

	virtual const char* getName			() const { return "symmetry"; }

	bool symmetryPropagationOnAnalyze(const Lit& p){
		bool propagatedBySymClasses = false;
        for(auto i=symClasses.begin(); !propagatedBySymClasses && i<symClasses.end(); i++){
        	propagatedBySymClasses = (*i)->isPropagated(p);
        }
        return propagatedBySymClasses;
	}

	void finishParsing(bool& present, bool& unsat) {
		parsing = false;
	    for(auto i=symmgroups.begin(); i<symmgroups.end(); ++i){
	    	symClasses.push_back(new SymVars(*i));
	    }
	}

	rClause notifypropagate(const Lit& l) {
	   	for(auto vs_it=symClasses.begin(); vs_it!=symClasses.end(); vs_it++){
			(*vs_it)->propagate(l,getPCSolver().getCurrentDecisionLevel(), getPCSolver());
		}
	   	return nullPtrClause;
	}

	void notifyBacktrack(int untillevel, const Lit& decision) {
		generatedConflict=false;
        for(auto vs_it=symClasses.begin(); vs_it!=symClasses.end(); ++vs_it){
        	(*vs_it)->backtrack(untillevel, decision);
		}
	}

	// Different symmetry strategy, TODO should be split into different class
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
		vec<Lit> newclause;
		bool allfalse = true;
		int level = 0;
		for (int i = 0; i < clause.size(); ++i) {
			auto it = symmetry.find(var(clause[i]));
			if (it == symmetry.end()) {
				newclause.push(clause[i]);
			} else {
				newclause.push(mkLit((*it).second, sign(clause[i])));
			}

			if (allfalse && getPCSolver().value(newclause.last()) == l_False) {
				int varlevel = getPCSolver().getLevel(var(newclause.last()));
				if (varlevel - 1 > level) {
					level = varlevel - 1;
				}
			} else {
				allfalse = false;
			}
		}

		if (allfalse) {
			if (level == 0) { //FIXME handle
				std::cerr << "Unsatisfiable symmetric clause, is not handled now.";
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
		for (int i = 0; i < clause.size(); ++i) {
			auto it = var2symmetries.find(var(clause[i]));
			if (it == var2symmetries.end()) {
				continue;
			}
			symmindices.insert((*it).second.begin(), (*it).second.end());
		}
		if (symmindices.size() > 0) {
			for (auto index = symmindices.begin(); noConflict && index != symmindices.end(); ++index) {
				noConflict = addSymmetricClause(clause, symmetries.at(*index));
			}
		}
		return noConflict;
	}

public:
	void add(const std::map<Var, Var>& symmetry){
		assert(parsing);
		symmetries.push_back(symmetry);
		for(auto i=symmetry.begin(); i!=symmetry.end(); ++i){
			var2symmetries[(*i).first].push_back(symmetries.size()-1);
		}
		// TODO Assume the grounding is perfectly symmetric according to all symmetries.
		// If this is not the case, during adding of symmetric clauses, conflicts might pop up
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

    bool notifyPropagate() {
		bool noConflict = true;
		adding = true;
		if (addedClauses.size() > 0) {
			for (auto it = addedClauses.begin(); noConflict && it != addedClauses.end(); ++it) {
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
