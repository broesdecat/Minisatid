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

	for (auto atom2rule : temprules) {
		std::vector<TempRule*> r;
		for (auto i = atom2rule.second.cbegin(); i != atom2rule.second.cend(); ++i) {
			if (not i->second->isagg) { // Add rule completion (NOTE has already been added earlier for aggregates)
				addFinishedRule(i->second);
			}
			r.push_back(i->second);
		}
		getIDSolver(atom2rule.first)->addRuleSet(r);
		deleteList<TempRule, Atom>(atom2rule.second);
	}
}

void Definition::addDefinedAggregate(const Aggregate& inneragg, const WLSet& innerset) {
	auto& def = rules[inneragg.defID];
	auto newrule = new TempRule(inneragg.onlyif, new Aggregate(inneragg), new WLSet(innerset));
	auto it = def.find(var(inneragg.head));
	if (it == def.cend()) {
		def[var(inneragg.head)] = newrule;
		return;
	}

	auto prevrule = it->second;
	if(inneragg.onlyif != prevrule->onlyif){
		throw idpexception("Rules on the same head in the same definition need to have the same semantics.");
	}
	if (prevrule->conjunctive) { // introduce new var (we need disjunctive root anyway
		auto newvar = solver->newAtom();
		def[newvar] = new TempRule(inneragg.onlyif, newvar, prevrule->conjunctive, prevrule->body);
		prevrule->conjunctive = false;
		prevrule->body = {mkLit(newvar)};
	}
	auto newvar = solver->newAtom();
	newrule->inneragg->head = mkPosLit(newvar);
	newrule->head = newvar;
	def[newvar] = newrule;
	prevrule->body.push_back(mkPosLit(newvar));
}

void Definition::addRule(bool onlyif, int defID, bool conj, Atom head, const litlist& ps) {
	auto& def = rules[defID];
	auto it = def.find(head);
	if (it == def.cend()) {
		def[head] = new TempRule(onlyif, head, conj, ps);
		return;
	}

	auto prevrule = it->second;
	if(onlyif != prevrule->onlyif){
		throw idpexception("Rules on the same head in the same definition need to have the same semantics.");
	}
	if (prevrule->conjunctive) { // introduce new var (we need disjunctive root anyway)
		auto newvar = solver->newAtom();
		def[newvar] = new TempRule(onlyif, newvar, prevrule->conjunctive, prevrule->body);
		prevrule->conjunctive = false;
		prevrule->body = {mkLit(newvar)};
	}
	if (conj) { // Create a new var and rule first
		auto newvar = solver->newAtom();
		def[newvar] = new TempRule(onlyif, newvar, conj, ps);
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
		Lit h = conj ? mkPosLit(head) : mkNegLit(head); //empty set conj = true, empty set disj = false
		Disjunction disj({ h });
		disj.theoryid = solver->getTheoryID();
		internalAdd(disj, solver->getTheoryID(), *solver);
	} else {
		conj = conj || rule->body.size() == 1; //rules with only one body atom are treated as conjunctive
		Implication eq(mkPosLit(head), rule->onlyif ? ImplicationType::IMPLIES: ImplicationType::EQUIVALENT, rule->body, conj);
		eq.theoryid = solver->getTheoryID();
		internalAdd(eq, solver->getTheoryID(), *solver);
	}
}
