#include "Definition.hpp"
#include "theorysolvers/PCSolver.hpp"
#include "IDSolver.hpp"

using namespace std;
using namespace MinisatID;

void Definition::addIDSolver(int id) {
	auto idsolver = new IDSolver(solver, id);
	idsolvers.insert( { id, idsolver });
}

// Call when grounding/parsing of all definitions is finished and they are in a consistent state
void Definition::addToPropagators() {
	for (auto ruleset = rules.cbegin(); ruleset != rules.cend(); ++ruleset) {
		std::vector<TempRule*> r;
		for (auto i = ruleset->second.cbegin(); i != ruleset->second.cend(); ++i) {
			if (not i->second->isagg) {
				addFinishedRule(i->second);
			}
			r.push_back(i->second);
		}
		getIDSolver(ruleset->first)->addRuleSet(r);
	}
}

void Definition::addDefinedAggregate(const InnerReifAggregate& inneragg, const InnerWLSet& innerset) {
	auto& def = rules[inneragg.defID];
	auto newrule = new TempRule(new InnerReifAggregate(inneragg), new InnerWLSet(innerset));
	auto it = def.find(inneragg.head);
	if (it == def.cend()) {
		def[inneragg.head] = newrule;
		return;
	}

	auto prevrule = it->second;
	if (prevrule->conjunctive) { // introduce new var (we need disjunctive root anyway
		auto newvar = solver->newVar();
		def[newvar] = new TempRule(newvar, prevrule->conjunctive, prevrule->body);
		prevrule->conjunctive = false;
		prevrule->body = {mkLit(newvar)};
	}
	auto newvar = solver->newVar();
	newrule->inneragg->head = newvar;
	newrule->head = newvar;
	def[newvar] = newrule;
	prevrule->body.push_back(mkPosLit(newvar));
}

void Definition::addRule(int defID, bool conj, Var head, const litlist& ps) {
	auto& def = rules[defID];
	auto it = def.find(head);
	if (it == def.cend()) {
		def[head] = new TempRule(head, conj, ps);
		return;
	}

	auto prevrule = it->second;
	if (prevrule->conjunctive) { // introduce new var (we need disjunctive root anyway)
		auto newvar = solver->newVar();
		def[newvar] = new TempRule(newvar, prevrule->conjunctive, prevrule->body);
		prevrule->conjunctive = false;
		prevrule->body = {mkLit(newvar)};
	}
	if (conj) { // Create a new var and rule first
		auto newvar = solver->newVar();
		def[newvar] = new TempRule(newvar, conj, ps);
		prevrule->body.push_back(mkPosLit(newvar));
	} else { // Disjunctive, so can add directly
		prevrule->body.insert(prevrule->body.end(), ps.cbegin(), ps.cend());
	}
}

void Definition::addFinishedRule(TempRule* rule) {
	MAssert(not rule->isagg);

	auto conj = rule->conjunctive;
	auto head = rule->head;

	if (rule->body.empty()) {
		Lit h = conj ? mkLit(head) : mkLit(head, true); //empty set conj = true, empty set disj = false
		InnerDisjunction v;
		v.literals.push_back(h);
		solver->add(v);
	} else {
		conj = conj || rule->body.size() == 1; //rules with only one body atom are treated as conjunctive

		InnerImplication eq(mkPosLit(head), ImplicationType::EQUIVALENT, rule->body, conj);
		solver->add(eq);
	}
}
