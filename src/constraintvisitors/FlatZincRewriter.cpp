/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Marien, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#include "external/FlatZincRewriter.hpp"

#include <cstdlib>
#include <vector>
#include <algorithm>

#include "external/Translator.hpp"

using namespace std;
using namespace MinisatID;

weightlist getWeigths(const WLSet& set) {
	weightlist ls;
	for (auto i = set.wl.cbegin(); i < set.wl.cend(); ++i) {
		ls.push_back(i->getWeight());
	}
	return ls;
}

litlist getLiterals(const WLSet& set) {
	litlist ls;
	for (auto i = set.wl.cbegin(); i < set.wl.cend(); ++i) {
		ls.push_back(i->getLit());
	}
	return ls;
}

/**
 * Missing support for constructs not present in FlatZinc: TODO
 * 		minimum, maximum and product optimization
 * 		subset minimization support
 * 		symmetries
 * 		count and alldiff (peter will have transformations for these)
 * 		recursively defined aggregates
 */
template<typename Stream>
FlatZincRewriter<Stream>::FlatZincRewriter(const SolverOption& modes, Stream& stream) :
		ExternalConstraintVisitor(modes, "flatzincrewriter"), Task(modes), state(SolverState::PARSING), _modes(modes), maxatomnumber(0), maxcpnumber(
				0), hasoptim(false), stream(stream) {
}
template<typename Stream>
FlatZincRewriter<Stream>::FlatZincRewriter(Remapper* remapper, Translator *translator, const SolverOption& modes, Stream& stream) :
		ExternalConstraintVisitor(remapper, translator, modes, "flatzincrewriter"), Task(modes), state(SolverState::PARSING), _modes(modes), maxatomnumber(
				0), maxcpnumber(0), hasoptim(false), stream(stream) {
}

template<typename Stream>
FlatZincRewriter<Stream>::~FlatZincRewriter() {
}

template<typename Stream>
std::ostream& FlatZincRewriter<Stream>::getOutput() {
	return stream;
}

template<typename Stream>
const WLSet& FlatZincRewriter<Stream>::getSet(uint i) const {
	if (sets.find(i) == sets.cend()) {
		throw idpexception("One of the aggregate sets was not declared before use.");
	}
	return sets.at(i);
}

//INVARIANT: always have already done a "check" operation on the Var
string getVarName(Atom Var) {
	stringstream ss;
	ss << "BOOL____" << Var;
	return ss.str();
}

string getVarName(const Lit& lit) {
	int value = var(lit);
	stringstream ss;
	if (isPositive(lit)) {
		ss << getVarName(var(lit));
	} else {
		ss << "BOOL_NEG" << value;
	}
	return ss.str();
}

string getIntVarName(VarID cpvar) {
	stringstream ss;
	ss << "INT__" << cpvar.id;
	return ss.str();
}

string getIntVarName(const Lit& lit) {
	int value = var(lit);
	stringstream ss;
	if (isPositive(lit)) {
		ss << "INT_BOOL_NEG_" << value;
	} else {
		ss << "INT_BOOL_" << value;
	}
	return ss.str();
}

void addDefAnnotation(int defID, ostream& stream) {
	stream << "::inductivelydefined(" << defID << ")";
}

template<typename Stream>
void FlatZincRewriter<Stream>::check(const Atom& Var) {
	check(mkPosLit(Var));
}

//INVARIANT: for a negative Lit, a bool var representing the positive Lit and an equivalence constraint will ALWAYS be added
template<typename Stream>
void FlatZincRewriter<Stream>::check(const Lit& lit) {
	int value = var(lit);
	set<uint>& seenset = isPositive(lit) ? atomsseen : negatomsseen;

	bool add = false;
	if (seenset.find(value) == seenset.cend()) {
		seenset.insert(value);
		add = true;
	}

	if (add) {
		if (maxatomnumber < (uint) std::abs(value)) {
			maxatomnumber = value;
		}

		definitions << "var bool: " << getVarName(lit);
		if (isParsing()) {
			definitions << "::output_var";
		}
		definitions << ";\n";

		if (not isPositive(lit)) { //also create positive one and add constraint (see invar)
			Lit poslit = mkPosLit(value);
			check(poslit);
			constraints << "constraint bool_not(" << getVarName(lit) << ", " << getVarName(~lit) << ");\n";
		}
	}
}

// Allows to add integer representation only once
template<typename Stream>
void FlatZincRewriter<Stream>::newIntVar(const Lit& lit, bool def, int defID) {
	int value = var(lit);
	set<uint>& seenset = isPositive(lit) ? litatomsseen : litnegatomsseen;

	if (seenset.find(value) == seenset.cend()) {
		seenset.insert(value);
		definitions << "var 0..1: " << getIntVarName(lit) << ";\n";
		constraints << "constraint int_eq_reif(" << getIntVarName(lit) << ", " << "1" << ", " << getVarName(lit) << ")";
		if (def) {
			addDefAnnotation(defID, constraints);
		}
		constraints << ";\n";
	}
}

template<typename Stream>
const Weight& FlatZincRewriter<Stream>::getMin(VarID var) {
	MAssert(varbounds.find(var)!=varbounds.cend());
	return (*varbounds.find(var)).second.first;
}

template<typename Stream>
const Weight& FlatZincRewriter<Stream>::getMax(VarID var) {
	MAssert(varbounds.find(var)!=varbounds.cend());
	return (*varbounds.find(var)).second.second;
}

template<typename Stream>
void FlatZincRewriter<Stream>::check(const vector<Lit>& lits) {
	for (auto i = lits.cbegin(); i < lits.cend(); ++i) {
		check(*i);
	}
}

template<typename Stream>
void FlatZincRewriter<Stream>::checkOnlyPos(const vector<Lit>& lits) {
	for (auto i = lits.cbegin(); i < lits.cend(); ++i) {
		check(var(*i));
	}
}

template<typename T>
void addMappedList(const vector<T>& list, ostream& stream) {
	bool begin = true;
	for (auto i = list.cbegin(); i < list.cend(); ++i) {
		if (!begin) {
			stream << ", ";
		}
		begin = false;
		stream << getVarName(*i);
	}
}

template<typename T>
void addIntVarList(const vector<T>& list, ostream& stream) {
	bool begin = true;
	for (auto i = list.cbegin(); i < list.cend(); ++i) {
		if (!begin) {
			stream << ", ";
		}
		begin = false;
		stream << getIntVarName(*i);
	}
}

template<typename T>
void addIntList(const vector<T>& list, ostream& stream) {
	bool begin = true;
	for (auto i = list.cbegin(); i < list.cend(); ++i) {
		if (!begin) {
			stream << ", ";
		}
		begin = false;
		stream << *i;
	}
}

template<typename Stream>
void FlatZincRewriter<Stream>::printRel(const string& left, const string& right, const Lit& head, const string& constr) {
	constraints << "constraint " << constr << "(" << left << ", " << right << ", " << getVarName(head) << ");\n";
}

template<typename Stream>
void FlatZincRewriter<Stream>::addBinRel(const string& left, const string& right, const Lit& head, EqType rel) {
	string constr;
	Lit h = head;
	switch (rel) {
	case EqType::EQ:
		constr = "int_eq_reif";
		break;
	case EqType::NEQ:
		constr = "int_ne_reif";
		break;
	case EqType::L:
		constr = "int_lt_reif";
		break;
	case EqType::G: {
		h = ~head;
		constr = "int_le_reif";
		break;
	}
	case EqType::GEQ: {
		h = ~head;
		constr = "int_lt_reif";
		break;
	}
	case EqType::LEQ:
		constr = "int_le_reif";
		break;
	}
	check(h);
	printRel(left, right, h, constr);
}

template<typename Stream>
void FlatZincRewriter<Stream>::printSum(const weightlist& weights, const string& vars, const Lit& head, string constr, string bound) {
	constraints << "constraint " << constr << "([";
	addIntList(weights, constraints);
	constraints << "],[" << vars << "], " << bound << ", " << getVarName(head) << ");\n";
}

template<typename Stream>
Atom FlatZincRewriter<Stream>::newAtom() {
	Atom lit = Atom(++maxatomnumber);
	check(lit);
	return lit;
}

template<typename Stream>
void FlatZincRewriter<Stream>::addSum(const weightlist& weights, const vector<VarID>& vars, const Lit& head, EqType rel, const Weight& bound) {
	stringstream ss;
	bool begin = true;
	for (auto i = vars.cbegin(); i < vars.cend(); ++i) {
		if (!begin) {
			ss << ", ";
		}
		begin = false;
		ss << getIntVarName(*i);
	}
	addSum(weights, ss.str(), head, rel, bound);
}

template<typename Stream>
void FlatZincRewriter<Stream>::addSum(const weightlist& weights, const string& vars, const Lit& head, EqType rel, const Weight& bound) {
	string constr = "";
	Weight newbound = bound;
	switch (rel) {
	case EqType::EQ:
		constr = "int_lin_eq_reif";
		break;
	case EqType::NEQ:
		constr = "int_lin_ne_reif";
		break;
	case EqType::L:
		constr = "int_lin_le_reif";
		newbound = bound - 1;
		break;
	case EqType::G: {
		Atom newhead = newAtom();
		constr = "int_lin_le_reif";
		constraints << "constraint bool_not(" << getVarName(head) << ", " << getVarName(newhead) << ");\n";
		break;
	}
	case EqType::GEQ: {
		Atom newhead = newAtom();
		constr = "int_lin_le_reif";
		newbound = bound - 1;
		constraints << "constraint bool_not(" << getVarName(head) << ", " << getVarName(newhead) << ");\n";
		break;
	}
	case EqType::LEQ:
		constr = "int_lin_le_reif";
		break;
	}

	stringstream ss;
	ss << newbound;

	printSum(weights, vars, head, constr, ss.str());
}

template<typename Stream>
void FlatZincRewriter<Stream>::addVarSum(const weightlist& weights, const vector<VarID>& vars, const Lit& head, EqType rel, VarID rhsvar) {
	vector<VarID> newvars = vars;
	newvars.push_back(rhsvar);

	weightlist newweights = weights;
	newweights.push_back(-1);

	addSum(newweights, newvars, head, rel, 0);
}

template<typename Stream>
void FlatZincRewriter<Stream>::addVarSum(const weightlist& weights, const litlist& lits, const Lit& head, EqType rel, VarID rhsvar) {
	stringstream ss;
	bool begin = true;
	for (auto i = lits.cbegin(); i < lits.cend(); ++i) {
		if (!begin) {
			ss << ", ";
		}
		begin = false;
		ss << getIntVarName(*i);
	}

	ss << ", " << getIntVarName(rhsvar);
	weightlist newweights = weights;
	newweights.push_back(-1);

	addSum(newweights, ss.str(), head, rel, 0);
}

template<typename Stream>
void FlatZincRewriter<Stream>::addSum(const Aggregate& agg, const WLSet& set) {
	for (auto i = set.wl.cbegin(); i < set.wl.cend(); ++i) {
		newIntVar(i->getLit(), agg.sem == AggSem::DEF, agg.defID);
	}

	Lit h = agg.head;
	Weight bound = agg.bound;
	if (agg.sign == AggSign::LB) { // Have to swap the sign, by adding the negated head and reducing bound
		h = ~agg.head;
		check(h);
		bound -= 1;
	}

	// add the constraint
	constraints << "constraint int_lin_le_reif([";
	addIntList(getWeigths(set), constraints);
	constraints << "], [";
	addIntVarList(getLiterals(set), constraints);
	constraints << "], " << bound << ", " << getVarName(h) << ");\n";
}

template<typename Stream>
VarID FlatZincRewriter<Stream>::newCpVar(const Weight& min, const Weight& max) {
	IntVarRange newvar({maxcpnumber + 1}, min, max);
	add(newvar);
	return newvar.varID;
}

template<typename Stream>
VarID FlatZincRewriter<Stream>::newCpVar(const std::vector<Weight>& values) {
	IntVarEnum newvar({maxcpnumber + 1}, values);
	add(newvar);
	return newvar.varID;
}

template<typename Stream>
VarID FlatZincRewriter<Stream>::addOptimization(bool& minimize) {
	minimize = true;
	if (savedvar.size() + savedagg.size() > 1) {
		throw idpexception("Transformation to flatzinc does not support prioritized optimization.");
	}
	VarID optimvar;
	if (savedagg.size() > 0) {
		auto mnm = savedagg[0];
		if (mnm.type != AggType::SUM && mnm.type != AggType::CARD) {
			throw idpexception("Optimization only supported on sum or cardinality aggregates.");
		}
		auto set = getSet(mnm.setid);
		Weight min = 0, max = 0;
		for (auto i = set.wl.cbegin(); i < set.wl.cend(); ++i) {
			auto w = i->getWeight();
			if (w < 0) {
				min += w;
			} else {
				max += w;
			}
		}

		optimvar = newCpVar(min, max);

		for (auto i = set.wl.cbegin(); i < set.wl.cend(); ++i) {
			newIntVar(i->getLit(), false, 0);
		}

		auto head = mkPosLit(newAtom());
		addVarSum(getWeigths(set), getLiterals(set), head, EqType::EQ, optimvar);
		Disjunction d({head});
		add(d);
	} else {
		MAssert(savedvar.size()>0);
		if(savedvar.size()>1){
			throw notYetImplemented("Optimization of multiple CP variables is not yet implemented.\n");
		}
		minimize = savedvar.front().minimize;
		optimvar = savedvar.front().varID;
	}
	return optimvar;
}

/**
 * Make a long list of products (shorten later by log series)
 * P <=> prod(v1*w1, ..., vn*wn) op b
 *
 * new vars vi' {1, wi}
 * vp1 = v1' * v2'
 * vp2 = vp1 * v3'
 * ...
 * vpn-1 = vpn-2 * vn'
 * P <=> vpn-1 op b
 */
template<typename Stream>
void FlatZincRewriter<Stream>::addProduct(const Aggregate& agg, const WLSet& set) {
	bool begin = true;
	Weight min = 1, max = 1;
	VarID prevvar;
	for (uint i = 0; i < set.wl.size(); ++i) {
		auto weight = set.wl[i].getWeight();

		if (weight == 1) { // TODO ugly hack to prevent problems with the equivalence of the intvar with the maxvalue (preventing the bool var to become false)
			continue;
		}

		auto varID = newCpVar({1,weight});
		constraints << "constraint int_eq_reif(" << getIntVarName(varID) << ", " << weight << ", " << getVarName(set.wl[i].getLit()) << ");\n";

		Weight prevmin = min;
		Weight prevmax = max;
		min = std::min(min, weight * prevmin);
		min = std::min(min, weight * prevmax);
		max = std::max(max, weight * prevmin);
		max = std::max(max, weight * prevmax);

		if (!begin) {
			auto newvar = newCpVar(min, max);
			constraints << "constraint int_times(" << getIntVarName(varID) << ", " << getIntVarName(prevvar) << ", " << getIntVarName(newvar) << ");\n";
			prevvar = newvar;
		} else {
			prevvar = varID;
		}
		begin = false;
	}

	stringstream ss;
	ss << agg.bound;
	addBinRel(getIntVarName(prevvar), ss.str(), agg.head, agg.sign == AggSign::LB ? EqType::GEQ : EqType::LEQ);
}

template<typename Stream>
void FlatZincRewriter<Stream>::execute() {
	state = SolverState::FINISHING;

	for (auto binrel : savedbinrels) {
		addBinRel(binrel.left, binrel.right, binrel.head, binrel.rel);
	}
	savedbinrels.clear();

	for (auto sum : savedcpsums) {
		// NOTE: Duplicate code with PropagatorFactory
		std::vector<VarID> newvars;
		for(auto i=0; i<sum.varIDs.size(); ++i){
			auto newvar = newCpVar(min(Weight(0),getMin(sum.varIDs[i])), max(Weight(0),getMax(sum.varIDs[i]))); // TODO: better make it an enum if 0 if far from the other values?
			newvars.push_back(newvar);
			auto tseitin0 = newAtom();
			auto tseitineq = newAtom();
			check(mkPosLit(tseitin0));
			add(Disjunction({sum.conditions[i], mkPosLit(tseitin0)}));
			stringstream ss;
			ss <<0;
			addBinRel(getIntVarName(newvar), ss.str(), mkPosLit(tseitin0), EqType::EQ);
			add(Disjunction({~sum.conditions[i], mkPosLit(tseitineq)}));
			check(mkPosLit(tseitineq));
			addBinRel(getIntVarName(newvar), getIntVarName(sum.varIDs[i]), mkPosLit(tseitineq), EqType::EQ);
		}
		addSum(sum.weights, newvars, sum.head, sum.rel, sum.bound);
	}
	savedcpsums.clear();

	for (auto agg : savedaggs) {
		if (agg.type == AggType::PROD) {
			addProduct(agg, getSet(agg.setID));
		} else {
			MAssert(agg.type==AggType::SUM || agg.type==AggType::CARD);
			addSum(agg, getSet(agg.setID));
		}
	}
	savedaggs.clear();

	getOutput() << definitions.str();
	getOutput() << constraints.str();
	if (hasoptim) {
		bool minimize = false;
		auto optimvar = addOptimization(minimize);
		if(minimize){
			getOutput() << "solve minimize " << getIntVarName(optimvar) << ";\n";
		}else{
			getOutput() << "solve maximize " << getIntVarName(optimvar) << ";\n";
		}
	} else {
		getOutput() << "solve satisfy;\n";
	}
	getOutput().flush();

	if(not savedbinrels.empty() || not savedcpsums.empty() || not savedaggs.empty()){
		throw idpexception("Invalid code path");
	}
}

// ADDITION METHODS

template<typename Stream>
void FlatZincRewriter<Stream>::addIntegerVar(VarID varID, const string& domainexpr, const Weight& min, const Weight& max) {
	if (cpvarsseen.find(varID) != cpvarsseen.cend()) {
		stringstream ss;
		ss << "Double addition of integer variable " << varID.id << ".";
		throw idpexception(ss.str());
	}

	definitions << "var " << domainexpr << ": " << getIntVarName(varID);
	if (isParsing()) {
		definitions << "::output_var";
	}
	definitions << ";\n";

	cpvarsseen.insert(varID);
	varbounds.insert(pair<VarID, pair<Weight, Weight> >(varID, pair<Weight, Weight>(min, max)));
	if (maxcpnumber < varID.id) {
		maxcpnumber = varID.id;
	}
}

template<typename Stream>
void FlatZincRewriter<Stream>::addEquiv(const Implication& implication, CloseConstraint close) {
	check(implication.body);
	check(implication.head);

	switch (implication.type) {
	case ImplicationType::EQUIVALENT:
		if (implication.conjunction) {
			constraints << "constraint array_bool_and([";
		} else {
			constraints << "constraint array_bool_or([";
		}
		addMappedList(implication.body, constraints);
		constraints << "], " << getVarName(implication.head) << ")";
		break;
	case ImplicationType::IMPLIES:
	case ImplicationType::IMPLIEDBY:
		auto clauses = implication.getEquivalentClauses();
		for(auto c: clauses){
			add(c);
		}
		break;
	}
	if (close == CLOSE) {
		constraints << ";\n";
	}
}

template<typename Stream>
void FlatZincRewriter<Stream>::addLits(const litlist& lits) {
	litlist pos, neg;
	for (auto i = lits.cbegin(); i < lits.cend(); ++i) {
		if (isPositive(*i)) {
			pos.push_back(*i);
		} else {
			neg.push_back(~(*i));
		}
	}

	check(pos);
	check(neg);

	constraints << "constraint bool_clause([";
	addMappedList(pos, constraints);
	constraints << "], [";
	addMappedList(neg, constraints);
	constraints << "]);\n";
}

template<typename Stream>
void FlatZincRewriter<Stream>::add(const Disjunction& sentence) {
	addLits(sentence.literals);
}

template<typename Stream>
void FlatZincRewriter<Stream>::add(const Implication& implic) {
	addEquiv(implic, CLOSE);
}

template<typename Stream>
void FlatZincRewriter<Stream>::add(const Rule& rule) {
	checkOnlyPos(rule.body);
	check(rule.head);

	if (not rule.conjunctive) {
		if (rule.body.size() > 1) {
			for (auto i = rule.body.cbegin(); i < rule.body.cend(); ++i) {
				add(Rule(rule.head, { *i }, true, rule.definitionID, rule.onlyif));
			}
		} else if (rule.body.size() == 0) {
			Disjunction clause({mkPosLit(rule.head)});
			add(clause);
		}
	}

	constraints << "constraint inductive_rule(";
	constraints << getVarName(rule.head) << ", ";

	constraints << "[";
	bool begin = true;
	for (auto i = rule.body.cbegin(); i < rule.body.cend(); ++i) {
		if (not isPositive(*i)) {
			continue;
		}
		if (!begin) {
			constraints << ", ";
		}
		begin = false;
		constraints << getVarName(*i);
	}
	constraints << "], ";

	constraints << "[";
	begin = true;
	for (auto i = rule.body.cbegin(); i < rule.body.cend(); ++i) {
		if (not isPositive(*i)) {
			continue;
		}
		if (!begin) {
			constraints << ", ";
		}
		begin = false;
		constraints << getVarName(~*i);
	}
	constraints << "], ";

	constraints << rule.definitionID;
	constraints << ");\n";
}

template<typename Stream>
void FlatZincRewriter<Stream>::add(const WLSet& set) {
	check(getLiterals(set));
	sets.insert(std::pair<int, WLSet>(set.setID, set));
}

template<typename Stream>
void FlatZincRewriter<Stream>::add(const Aggregate& origagg) {
	check(origagg.head);

	if (origagg.type == AggType::PROD) {
		MAssert(isParsing());
		savedaggs.push_back(origagg);
	} else if (origagg.type == AggType::CARD || origagg.type == AggType::SUM) {
		MAssert(isParsing());
		savedaggs.push_back(origagg);
	} else { // MIN or MAX
		Aggregate agg(origagg);
		auto set = getSet(agg.setID);

		// Transform min into max
		if (agg.type == AggType::MIN) {
			for (weightlist::size_type i = 0; i < set.wl.size(); ++i) {
				set.wl[i] = WLtuple(set.wl[i].getLit(), -set.wl[i].getWeight());
			}

			agg.bound = -agg.bound;
			agg.sign = agg.sign == AggSign::LB ? AggSign::UB : AggSign::LB;
		}

		bool ub = agg.sign == AggSign::UB;
		litlist lits;
		for (weightlist::size_type i = 0; i < set.wl.size(); i++) {
			if (set.wl[i].getWeight() < agg.bound) {
				continue;
			}
			if (ub && set.wl[i].getWeight() == agg.bound) {
				continue;
			}
			lits.push_back(ub ? ~set.wl[i].getLit() : set.wl[i].getLit());
		}

		addEquiv(Implication(agg.head, ImplicationType::EQUIVALENT, lits, ub), OPEN);
		if (agg.sem == AggSem::DEF) {
			addDefAnnotation(agg.defID, constraints);
		}
		constraints << ";\n";
	}
}

template<typename Stream>
void FlatZincRewriter<Stream>::add(const OptimizeVar& mnm) {
	MAssert(isParsing());
	hasoptim = true;
	savedvar.push_back(mnm);
}

template<typename Stream>
void FlatZincRewriter<Stream>::add(const MinimizeAgg& mnm) {
	MAssert(isParsing());
	hasoptim = true;
	savedagg.push_back(mnm);
}

template<typename Stream>
void FlatZincRewriter<Stream>::add(const IntVarEnum& var) {
	if(var.partial){
		throw idpexception("Cannot use partial constants in flatzinc.");
	}
	stringstream ss;
	ss << "{";
	bool begin = true;
	for (auto i = var.values.cbegin(); i < var.values.cend(); ++i) {
		if (!begin) {
			ss << ", ";
		}
		begin = false;
		ss << *i;
	}
	ss << "}";

	Weight min = var.values[0], max = var.values[0];
	for (uint i = 1; i < var.values.size(); ++i) {
		const Weight& w = var.values[i];
		if (w < min) {
			min = w;
		}
		if (w > max) {
			max = w;
		}
	}
	addIntegerVar(var.varID, ss.str(), min, max);
}

template<typename Stream>
void FlatZincRewriter<Stream>::add(const IntVarRange& var) {
	if(var.partial){
		throw idpexception("Cannot use partial constants in flatzinc.");
	}
	stringstream ss;
	ss << var.minvalue << ".." << var.maxvalue;
	addIntegerVar(var.varID, ss.str(), var.minvalue, var.maxvalue);
}

template<typename Stream>
void FlatZincRewriter<Stream>::add(const CPBinaryRel& rel) {
	MAssert(isParsing());
	check(rel.head);

	stringstream ss;
	ss << rel.bound;
	BinRel binrel = {rel.head, getIntVarName(rel.varID), ss.str(), rel.rel};
	savedbinrels.push_back(binrel);
}

template<typename Stream>
void FlatZincRewriter<Stream>::add(const CPBinaryRelVar& rel) {
	MAssert(isParsing());
	check(rel.head);

	BinRel binrel = {rel.head, getIntVarName(rel.lhsvarID), getIntVarName(rel.rhsvarID), rel.rel};
	savedbinrels.push_back(binrel);
}

template<typename Stream>
void FlatZincRewriter<Stream>::add(const CPSumWeighted& sum) {
	MAssert(isParsing());

	check(sum.head);
	for(auto l: sum.conditions){
		check(l);
	}
	savedcpsums.push_back(sum);
}

// Explicit instantiations. Note, apparently, they have to be AT THE END of the cpp
template class MinisatID::FlatZincRewriter<std::ostream> ;
