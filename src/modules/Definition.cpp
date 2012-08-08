#include "Definition.hpp"
#include "IDSolver.hpp"
#include "external/utils/ContainerUtils.hpp"

using namespace std;
using namespace MinisatID;

void Definition::addIDSolver(int id) {
	auto idsolver = new IDSolver(solver, id);
	idsolvers.insert( { id, idsolver });
}

// Call when grounding/parsing of all definitions is finished and they are in a consistent state
void Definition::addToPropagators() {
	auto temprules = rules; // NOTE: copy set because adding rule might trigger more grounding and new rules, which should NOT be added to the same datastructures
	rules.clear();

	for (auto ruleset = temprules .begin(); ruleset != temprules .end(); ++ruleset) {
		std::vector<TempRule*> r;
		for (auto i = ruleset->second.cbegin(); i != ruleset->second.cend(); ++i) {
			if (not i->second->isagg) {
				addFinishedRule(i->second);
			}
			r.push_back(i->second);
		}
		getIDolver(ruleset->first)->addRuleSet(r);
		deleteList<TempRule, Atom>(ruleset->second);
	}
}

void Definition::addDefinedAggregate(uint id, const Aggregate& inneragg, const WLSet& innerset) {
	auto& def = rules[inneragg.defID];
	auto newrule = new TempRule(id, new Aggregate(inneragg), new WLSet(innerset));
	auto it = def.find(var(inneragg.head));
	if (it == def.cend()) {
		def[var(inneragg.head)] = newrule;
		return;
	}

	auto prevrule = it->second;
	if (prevrule->conjunctive) { // introduce new var (we need disjunctive root anyway
		auto newvar = solver->newVar();
		def[newvar] = new TempRule(id, newvar, prevrule->conjunctive, prevrule->body);
		prevrule->conjunctive = false;
		prevrule->body = {mkLit(newvar)};
	}
	auto newvar = solver->newVar();
	newrule->inneragg->head = mkPosLit(newvar);
	newrule->head = newvar;
	def[newvar] = newrule;
	prevrule->body.push_back(mkPosLit(newvar));
}

void Definition::addRule(uint id, int defID, bool conj, Atom head, const litlist& ps) {
	auto& def = rules[defID];
	auto it = def.find(head);
	if (it == def.cend()) {
		def[head] = new TempRule(id, head, conj, ps);
		return;
	}

	auto prevrule = it->second;
	if (prevrule->conjunctive) { // introduce new var (we need disjunctive root anyway)
		auto newvar = solver->newVar();
		def[newvar] = new TempRule(id, newvar, prevrule->conjunctive, prevrule->body);
		prevrule->conjunctive = false;
		prevrule->body = {mkLit(newvar)};
	}
	if (conj) { // Create a new var and rule first
		auto newvar = solver->newVar();
		def[newvar] = new TempRule(id, newvar, conj, ps);
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
		Disjunction disj(rule->id, {h});
		disj.theoryid = solver->getTheoryID();
		internalAdd(disj, solver->getTheoryID(), *solver);
	} else {
		conj = conj || rule->body.size() == 1; //rules with only one body atom are treated as conjunctive
		Implication eq(rule->id, mkPosLit(head), ImplicationType::EQUIVALENT, rule->body, conj);
		eq.theoryid = solver->getTheoryID();
		internalAdd(eq, solver->getTheoryID(), *solver);
	}
}
