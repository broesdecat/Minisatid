/************************************
	Definition.hpp
	this file belongs to GidL 2.0
	(c) K.U.Leuven
************************************/

#ifndef DEFINITION_HPP_
#define DEFINITION_HPP_

#include "external/ExternalUtils.hpp"

namespace MinisatID{

class PCSolver;

struct TempRule{
	uint id;
	Atom head;
	std::vector<Lit> body;
	bool conjunctive;

	bool isagg;
	Aggregate* inneragg;
	WLSet* innerset;

	TempRule(uint id, Atom head, bool conjunctive, std::vector<Lit> body): id(id), head(head), body(body), conjunctive(conjunctive), isagg(false), inneragg(NULL), innerset(NULL){}
	TempRule(uint id, Aggregate* inneragg, WLSet* innerset): id(id), head(var(inneragg->head)), isagg(true), inneragg(inneragg), innerset(innerset){
		MAssert(isPositive(inneragg->head));
		MAssert(inneragg->sem==AggSem::DEF);
	}

	~TempRule(){
		if(isagg){
			delete(inneragg);
			delete(innerset);
		}
	}
};

class IDSolver;

typedef std::vector<Lit> litlist;

class Definition{
private:
	std::map<int, IDSolver*> idsolvers;

	bool hasIDSolver(int id) const {
		return idsolvers.find(id) != idsolvers.cend();
	}

	IDSolver* getIDolver(int id) {
		if (!hasIDSolver(id)) {
			addIDSolver(id);
		}
		return idsolvers.at(id);
	}

	void addIDSolver(int id);

	PCSolver* solver;

	std::map<int, std::map<Atom, TempRule*> > rules;

public:
	Definition(PCSolver* solver): solver(solver){

	}

	// Call when grounding/parsing of all definitions is finished and they are in a consistent state
	void addToPropagators();

	void addDefinedAggregate(uint id, const Aggregate& inneragg, const WLSet& innerset);
	void addRule(uint id, int defID, bool conj, Atom head, const litlist& ps);

private:
	void addFinishedRule(TempRule* rule);
};
}


#endif /* DEFINITION_HPP_ */
