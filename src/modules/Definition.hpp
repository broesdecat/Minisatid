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
	Var head;
	std::vector<Lit> body;
	bool conjunctive;

	bool isagg;
	InnerReifAggregate* inneragg;
	InnerWLSet* innerset;

	TempRule(Var head, bool conjunctive, std::vector<Lit> body): head(head), body(body), conjunctive(conjunctive), isagg(false), inneragg(NULL), innerset(NULL){}
	TempRule(InnerReifAggregate* inneragg, InnerWLSet* innerset): head(inneragg->head), isagg(true), inneragg(inneragg), innerset(innerset){}

	~TempRule(){
		if(isagg){
			delete(inneragg);
			delete(innerset);
		}
	}
};

class Definition{
	PCSolver* solver;
	PCSolver& getPCSolver() {
		return *solver;
	}
	std::map<Var, TempRule*> rules;
	void addToPropagator(IDSolver* idsolver){
		std::vector<TempRule*> r;
		for(auto i=rules.cbegin(); i<rules.cend(); ++i) {
			if(not i->second->isagg){
				addFinishedRule(i->second);
			}
			r.push_back(i->second);
		}
		idsolver->addRuleSet(r);
	}

	void addDefinedAggregate(const InnerReifAggregate& inneragg, const InnerWLSet& innerset) {
		auto newrule = new TempRule(new InnerReifAggregate(inneragg), new InnerWLSet(innerset));
		auto it = rules.find(inneragg.head);
		if (it == rules.cend()) {
			rules[inneragg.head] = newrule;
			return;
		}

		auto prevrule = it->second;
		if (prevrule->conjunctive) { // introduce new var (we need disjunctive root anyway
			auto newvar = getPCSolver().newVar();
			rules[newvar] = new TempRule(newvar, prevrule->conjunctive, prevrule->body);
			prevrule->conjunctive = false;
			prevrule->body = {mkLit(newvar)};
		}
		auto newvar = getPCSolver().newVar();
		newrule->inneragg->head = newvar;
		newrule->head = newvar;
		rules[newvar] = newrule;
		prevrule->body.push_back(mkPosLit(newvar));
	}

	void addRule(bool conj, Var head, const litlist& ps) {
		auto it = rules.find(head);
		if (it == rules.cend()) {
			rules[head] = new TempRule(head, conj, ps);
			return;
		}

		auto prevrule = it->second;
		if (prevrule->conjunctive) { // introduce new var (we need disjunctive root anyway)
			auto newvar = getPCSolver().newVar();
			rules[newvar] = new TempRule(newvar, prevrule->conjunctive, prevrule->body);
			prevrule->conjunctive = false;
			prevrule->body = {mkLit(newvar)};
		}
		if (conj) { // Create a new var and rule first
			auto newvar = getPCSolver().newVar();
			rules[newvar] = new TempRule(newvar, conj, ps);
			prevrule->body.push_back(mkPosLit(newvar));
		} else { // Disjunctive, so can add directly
			prevrule->body.insert(prevrule->body.end(), ps.cbegin(), ps.cend());
		}
	}

	void addFinishedRule(TempRule* rule) {
		MAssert(not rule->isagg);

		auto conj = rule->conjunctive;
		auto head = rule->head;

		if (rule->body.empty()) {
			Lit h = conj ? mkLit(head) : mkLit(head, true); //empty set conj = true, empty set disj = false
			InnerDisjunction v;
			v.literals.push_back(h);
			getPCSolver().add(v);
		} else {
			conj = conj || rule->body.size() == 1; //rules with only one body atom are treated as conjunctive

			InnerImplication eq(mkPosLit(head), ImplicationType::EQUIVALENT, rule->body, conj);
			getPCSolver().add(eq);
		}
	}
};
}


#endif /* DEFINITION_HPP_ */
