/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#include "FlatZincRewriter.hpp"

#include <cstdlib>
#include <vector>
#include <algorithm>

#include "external/Translator.hpp"

using namespace std;
using namespace MinisatID;

weightlist getWeigths(const InnerWLSet& set){
	weightlist ls;
	for(auto i=set.wls.cbegin(); i<set.wls.cend(); ++i) {
		ls.push_back(i->getWeight());
	}
	return ls;
}

litlist getLiterals(const InnerWLSet& set){
	litlist ls;
	for(auto i=set.wls.cbegin(); i<set.wls.cend(); ++i) {
		ls.push_back(i->getLit());
	}
	return ls;
}

/**
 * TODO add support for constructs not present in Flatzinc
 * 		minimum, maximum and product optimization
 * 		subset minimization support
 * 		count and alldiff (peter will have transformations for these)
 * 		recursively defined aggregates
 */
template<typename Stream>
FlatZincRewriter<Stream>::FlatZincRewriter(LiteralPrinter* pcsolver, const SolverOption& modes, Stream& stream):
		ConstraintAdditionMonitor<Stream>(pcsolver, stream),
		state(SolverState::PARSING), _modes(modes), maxatomnumber(0), maxcpnumber(0), optim(MNMZ_NONE),
		stream(stream){
}

template<typename Stream>
FlatZincRewriter<Stream>::~FlatZincRewriter() {
}

template<typename Stream>
std::ostream& FlatZincRewriter<Stream>::getOutput() {
	return stream;
}

template<typename Stream>
const InnerWLSet& FlatZincRewriter<Stream>::getSet(uint i) const {
	if (sets.find(i)==sets.cend()) {
		throw idpexception("One of the aggregate sets was not declared before use.");
	}
	return sets.at(i);
}

//INVARIANT: always have already done a "check" operation on the Var
string getVarName(Var Var) {
	stringstream ss;
	ss << "BOOL____" << Var;
	return ss.str();
}

string getVarName(const Lit& lit) {
	int value = var(lit);
	stringstream ss;
	if(isPositive(lit)){
		ss << getVarName(var(lit));
	}else{
		ss << "BOOL_NEG" << value;
	}
	return ss.str();
}

string getIntVarName(int cpvar) {
	stringstream ss;
	ss << "INT__" << cpvar;
	return ss.str();
}

string getIntVarName(const Lit& lit) {
	int value = var(lit);
	stringstream ss;
	if(isPositive(lit)){
		ss << "INT_BOOL_NEG_" << value;
	}else{
		ss << "INT_BOOL_" << value;
	}
	return ss.str();
}

void addDefAnnotation(int defID, ostream& stream) {
	stream << "::inductivelydefined(" << defID << ")";
}

template<typename Stream>
void FlatZincRewriter<Stream>::check(const Var& Var) {
	check(mkPosLit(Var));
}

//INVARIANT: for a negative Lit, a bool var representing the positive Lit and an equivalence constraint will ALWAYS be added
template<typename Stream>
void FlatZincRewriter<Stream>::check(const Lit& lit) {
	int value = var(lit);
	set<uint>& seenset = isPositive(lit)? atomsseen : negatomsseen;

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
void FlatZincRewriter<Stream>::createIntVar(const Lit& lit, bool def, int defID) {
	int value = var(lit);
	set<uint>& seenset = isPositive(lit)? litatomsseen:litnegatomsseen;

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
const Weight& FlatZincRewriter<Stream>::getMin(uint var) {
	assert(varbounds.find(var)!=varbounds.cend());
	return (*varbounds.find(var)).second.first;
}

template<typename Stream>
const Weight& FlatZincRewriter<Stream>::getMax(uint var) {
	assert(varbounds.find(var)!=varbounds.cend());
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
void FlatZincRewriter<Stream>::printSum(const weightlist& weights, const string& vars, Var head, string constr, string bound) {
	constraints << "constraint " << constr << "([";
	addIntList(weights, constraints);
	constraints << "],[" << vars << "], " << bound << ", " << getVarName(head) << ");\n";
}

template<typename Stream>
Var FlatZincRewriter<Stream>::createAtom() {
	Var lit = Var(maxatomnumber + 1);
	check(lit);
	return lit;
}

template<typename Stream>
void FlatZincRewriter<Stream>::addSum(const weightlist& weights, const vector<uint>& vars, Var head, EqType rel, const Weight& bound) {
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
void FlatZincRewriter<Stream>::addSum(const weightlist& weights, const string& vars, Var head, EqType rel, const Weight& bound) {
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
		Var newhead = createAtom();
		constr = "int_lin_le_reif";
		constraints << "constraint bool_not(" << getVarName(head) << ", " << getVarName(newhead) << ");\n";
		break;
	}
	case EqType::GEQ: {
		Var newhead = createAtom();
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
void FlatZincRewriter<Stream>::addVarSum(const weightlist& weights, const vector<uint>& vars, Var head, EqType rel, uint rhsvar) {
	vector<uint> newvars = vars;
	newvars.push_back(rhsvar);

	weightlist newweights = weights;
	newweights.push_back(-1);

	addSum(newweights, newvars, head, rel, 0);
}

template<typename Stream>
void FlatZincRewriter<Stream>::addVarSum(const weightlist& weights, const litlist& lits, Var head, EqType rel, uint rhsvar) {
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
void FlatZincRewriter<Stream>::addSum(const InnerReifAggregate& agg, const InnerWLSet& set) {
	for (auto i = set.wls.cbegin(); i < set.wls.cend(); ++i) {
		createIntVar(i->getLit(), agg.sem == AggSem::DEF, agg.defID);
	}

	Lit h = mkPosLit(agg.head);
	Weight bound = agg.bound;
	if (agg.sign == AggSign::LB) { // Have to swap the sign, by adding the negated head and reducing bound
		h = mkPosLit(agg.head);
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
uint FlatZincRewriter<Stream>::createCpVar(const Weight& min, const Weight& max) {
	InnerIntVarRange newvar;
	newvar.varID = maxcpnumber + 1;
	newvar.minvalue = min;
	newvar.maxvalue = max;
	visit(newvar);
	return newvar.varID;
}

template<typename Stream>
uint FlatZincRewriter<Stream>::createCpVar(const std::vector<Weight>& values) {
	InnerIntVarEnum newvar;
	newvar.varID = maxcpnumber + 1;
	newvar.values = values;
	visit(newvar);
	return newvar.varID;
}

template<typename Stream>
uint FlatZincRewriter<Stream>::addOptimization() {
	uint optimvar = 0;
	if (optim == MNMZ_AGG) {
		auto mnm = savedagg;
		if (mnm.type != AggType::SUM && mnm.type != AggType::CARD) {
			throw idpexception("Optimization only supported on sum or cardinality aggregates.");
		}
		auto set = getSet(mnm.setID);
		Weight min = 0, max = 0;
		for (auto i = set.wls.cbegin(); i < set.wls.cend(); ++i) {
			auto w = i->getWeight();
			if (w < 0) {
				min += w;
			} else {
				max += w;
			}
		}

		optimvar = createCpVar(min, max);

		for (auto i = set.wls.cbegin(); i < set.wls.cend(); ++i) {
			createIntVar(i->getLit(), false, 0);
		}

		auto head = createAtom();
		addVarSum(getWeigths(set), getLiterals(set), head, EqType::EQ, optimvar);
		InnerDisjunction d;
		d.literals.push_back(mkPosLit(head));
		visit(d);
	} else if (optim == MNMZ_LIST) {
		auto mnm = savedlistmnmz;

		optimvar = createCpVar(1, long(mnm.literals.size()));

		int currentvalue = 1;
		for (auto i = mnm.literals.cbegin(); i < mnm.literals.cend(); ++i) {
			stringstream ss;
			ss << currentvalue;
			addBinRel(getVarName(optimvar), ss.str(), *i, EqType::EQ);
			currentvalue++;
		}
	} else if (optim == MNMZ_SUBSET) {
		throw idpexception("Subset minimization is not supported by the FlatZinc language.");
	} else {
		throw notYetImplemented("Optimization of a CP variable is not yet implemented.\n");
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
void FlatZincRewriter<Stream>::addProduct(const InnerReifAggregate& agg, const InnerWLSet& set) {
	bool begin = true;
	Weight min = 1, max = 1;
	uint prevvar = 0;
	for (uint i = 0; i < set.wls.size(); ++i) {
		auto weight = set.wls[i].getWeight();

		if (weight == 1) { // FIXME ugly hack to prevent problems with the equivalence of the intvar with the maxvalue (preventing the bool var to become false)
			continue;
		}

		vector<Weight> weights;
		weights.push_back(1);
		weights.push_back(weight);

		uint varID = createCpVar(weights);
		constraints << "constraint int_eq_reif(" << getVarName(varID) << ", " << weight << ", " << getVarName(set.wls[i].getLit()) << ");\n";

		Weight prevmin = min;
		Weight prevmax = max;
		min = std::min(min, weight * prevmin);
		min = std::min(min, weight * prevmax);
		max = std::max(max, weight * prevmin);
		max = std::max(max, weight * prevmax);

		if (!begin) {
			uint newvar = createCpVar(min, max);
			constraints << "constraint int_times(" << getVarName(varID) << ", " << getVarName(prevvar) << ", " << getVarName(newvar) << ");\n";
			prevvar = newvar;
		} else {
			prevvar = varID;
		}
		begin = false;
	}

	stringstream ss;
	ss << agg.bound;
	addBinRel(getVarName(prevvar), ss.str(), mkPosLit(agg.head), agg.sign == AggSign::LB ? EqType::GEQ : EqType::LEQ);
}

template<typename Stream>
void FlatZincRewriter<Stream>::finishParsing() {
	state = SolverState::FINISHING;

	for (auto i = savedbinrels.cbegin(); i < savedbinrels.cend(); ++i) {
		addBinRel((*i).left, (*i).right, mkPosLit((*i).head), (*i).rel);
	}

	for (auto i = savedcpsums.cbegin(); i < savedcpsums.cend(); ++i) {
		addSum((*i).weights, (*i).varIDs, (*i).head, (*i).rel, (*i).bound);
	}

	for (auto i = savedaggs.cbegin(); i < savedaggs.cend(); ++i) {
		if ((*i).type == AggType::PROD) {
			addProduct(*i, getSet((*i).setID));
		} else {
			assert((*i).type==AggType::SUM || (*i).type==AggType::CARD);
			addSum(*i, getSet((*i).setID));
		}
	}

	getOutput() << definitions.str();
	getOutput() << constraints.str();
	if (optim != MNMZ_NONE) {
		uint optimvar = addOptimization();
		getOutput() << "solve minimize " << getVarName(optimvar) << ";\n";
	} else {
		getOutput() << "solve satisfy;\n";
	}
}

// ADDITION METHODS

template<typename Stream>
void FlatZincRewriter<Stream>::addIntegerVar(uint varID, const string& domainexpr, const Weight& min, const Weight& max) {
	if (cpvarsseen.find(varID) != cpvarsseen.cend()) {
		stringstream ss;
		ss << "Double addition of integer variable " << varID << ".";
		throw idpexception(ss.str());
	}

	definitions << "var " << domainexpr << ": " << getVarName(varID);
	if (isParsing()) {
		definitions << "::output_var";
	}
	definitions << ";\n";

	cpvarsseen.insert(varID);
	varbounds.insert(pair<uint, pair<Weight, Weight> >(varID, pair<Weight, Weight>(min, max)));
	if (maxcpnumber < varID) {
		maxcpnumber = varID;
	}
}

template<typename Stream>
void FlatZincRewriter<Stream>::addEquiv(const InnerImplication& implication, CloseConstraint close) {
	check(implication.literals);
	check(implication.head);

	switch (implication.type) {
	case ImplicationType::EQUIVALENT:
		if (implication.conjunctive) {
			constraints << "constraint array_bool_and([";
		} else {
			constraints << "constraint array_bool_or([";
		}
		addMappedList(implication.literals, constraints);
		constraints << "], " << getVarName(implication.head) << ")";
		break;
	case ImplicationType::IMPLIES:
		if (implication.conjunctive) {
			InnerDisjunction d;
			d.literals.resize(2, not implication.head);
			for (auto i = implication.literals.cbegin(); i < implication.literals.cend(); ++i) {
				d.literals[1] = *i;
				visit(d);
			}
		} else {
			InnerDisjunction d;
			d.literals.insert(d.literals.begin(), implication.literals.cbegin(), implication.literals.cend());
			d.literals.push_back(not implication.head);
			visit(d);
		}
		break;
	case ImplicationType::IMPLIEDBY:
		if (implication.conjunctive) {
			InnerDisjunction d;
			for (auto i = implication.literals.cbegin(); i < implication.literals.cend(); ++i) {
				d.literals.push_back(not *i);
			}
			d.literals.push_back(implication.head);
			visit(d);
		} else {
			InnerDisjunction d;
			d.literals.resize(2, implication.head);
			for (auto i = implication.literals.cbegin(); i < implication.literals.cend(); ++i) {
				d.literals[1] = *i;
				visit(d);
			}
		}
		break;
	}
	if (close == CLOSE) {
		constraints << ";\n";
	}
}

template<typename Stream>
void FlatZincRewriter<Stream>::add(const litlist& lits) {
	litlist pos, neg;
	for (auto i = lits.cbegin(); i < lits.cend(); ++i) {
		if(isPositive(*i)){
			pos.push_back(*i);
		}else{
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
void FlatZincRewriter<Stream>::visit(const InnerDisjunction& sentence) {
	add(sentence.literals);
}

template<typename Stream>
void FlatZincRewriter<Stream>::visit(const InnerImplication& implic) {
	addEquiv(implic, CLOSE);
}

template<typename Stream>
void FlatZincRewriter<Stream>::visit(const InnerRule& rule) {
	checkOnlyPos(rule.body);
	check(rule.head);

	if (!rule.conjunctive) {
		if (rule.body.size() > 1) {
			for (auto i = rule.body.cbegin(); i < rule.body.cend(); ++i) {
				InnerRule smallrule;
				smallrule.head = rule.head;
				smallrule.body.push_back(*i);
				smallrule.conjunctive = true;
				smallrule.definitionID = rule.definitionID;
				visit(smallrule);
			}
		} else if (rule.body.size() == 0) {
			InnerDisjunction clause;
			clause.literals.push_back(mkPosLit(rule.head));
			visit(clause);
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
void FlatZincRewriter<Stream>::visit(const InnerWLSet& set) {
	check(getLiterals(set));
	sets.insert(std::pair<int, InnerWLSet>(set.setID, set));
}

template<typename Stream>
void FlatZincRewriter<Stream>::visit(const InnerAggregate&) {
	throw notYetImplemented("Non-reif aggregate addition.\n");
}

template<typename Stream>
void FlatZincRewriter<Stream>::visit(const InnerForcedChoices&) {
	throw idpexception("Forcedchoices are unsupported by flatzinc.\n");
}

template<typename Stream>
void FlatZincRewriter<Stream>::visit(const InnerSymmetry&) {
	throw idpexception("Symmetries are unsupported by flatzinc.\n"); // TODO maybe they are?
}

template<typename Stream>
void FlatZincRewriter<Stream>::visit(const InnerReifAggregate& origagg) {
	check(origagg.head);

	if (origagg.type == AggType::PROD) {
		assert(isParsing());
		savedaggs.push_back(origagg);
	} else if (origagg.type == AggType::CARD || origagg.type == AggType::SUM) {
		assert(isParsing());
		savedaggs.push_back(origagg);
	} else { // MIN or MAX
		InnerReifAggregate agg(origagg);
		auto set = getSet(agg.setID);

		// Transform min into max
		if (agg.type == AggType::MIN) {
			for (weightlist::size_type i = 0; i < set.wls.size(); ++i) {
				set.wls[i] = WL(set.wls[i].getLit(), -set.wls[i].getWeight());
			}

			agg.bound = -agg.bound;
			agg.sign = agg.sign == AggSign::LB ? AggSign::UB : AggSign::LB;
		}

		bool ub = agg.sign == AggSign::UB;
		litlist lits;
		for (weightlist::size_type i = 0; i < set.wls.size(); i++) {
			if (set.wls[i].getWeight() < agg.bound) {
				continue;
			}
			if (ub && set.wls[i].getWeight() == agg.bound) {
				continue;
			}
			lits.push_back(ub ? ~set.wls[i].getLit() : set.wls[i].getLit());
		}

		addEquiv(InnerImplication(mkPosLit(agg.head), ImplicationType::EQUIVALENT, lits, ub), OPEN);
		if (agg.sem == AggSem::DEF) {
			addDefAnnotation(agg.defID, constraints);
		}
		constraints << ";\n";
	}
}

template<typename Stream>
void FlatZincRewriter<Stream>::visit(const InnerMinimizeSubset& sentence) {
	assert(isParsing());
	optim = MNMZ_SUBSET;
	savedsubsetmnmz = sentence;
	check(sentence.literals);
}

template<typename Stream>
void FlatZincRewriter<Stream>::visit(const InnerMinimizeOrderedList& sentence) {
	assert(isParsing());
	optim = MNMZ_LIST;
	check(sentence.literals);
	savedlistmnmz = sentence;
}

template<typename Stream>
void FlatZincRewriter<Stream>::visit(const InnerMinimizeVar& mnm) {
	assert(isParsing());
	savedvar = mnm;
	optim = MNMZ_VAR;
}

template<typename Stream>
void FlatZincRewriter<Stream>::visit(const InnerMinimizeAgg& mnm) {
	assert(isParsing());
	savedagg = mnm;
	optim = MNMZ_AGG;
}

template<typename Stream>
void FlatZincRewriter<Stream>::visit(const InnerIntVarEnum& var) {
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
void FlatZincRewriter<Stream>::visit(const InnerIntVarRange& var) {
	stringstream ss;
	ss << var.minvalue << ".." << var.maxvalue;
	addIntegerVar(var.varID, ss.str(), var.minvalue, var.maxvalue);
}

template<typename Stream>
void FlatZincRewriter<Stream>::visit(const InnerCPBinaryRel& rel) {
	assert(isParsing());
	check(rel.head);

	BinRel binrel;
	binrel.left = getVarName(rel.varID);
	stringstream ss;
	ss << rel.bound;
	binrel.right = ss.str();
	binrel.head = rel.head;
	binrel.rel = rel.rel;
	savedbinrels.push_back(binrel);
}

template<typename Stream>
void FlatZincRewriter<Stream>::visit(const InnerCPBinaryRelVar& rel) {
	assert(isParsing());
	check(rel.head);

	BinRel binrel;
	binrel.left = getVarName(rel.lhsvarID);
	binrel.right = getVarName(rel.rhsvarID);
	binrel.head = rel.head;
	binrel.rel = rel.rel;
	savedbinrels.push_back(binrel);
}

template<typename Stream>
void FlatZincRewriter<Stream>::visit(const InnerCPSumWeighted& sum) {
	assert(isParsing());
	check(sum.head);
	savedcpsums.push_back(sum);
}

template<typename Stream>
void FlatZincRewriter<Stream>::visit(const InnerCPCount&) {
	throw idpexception("Count constraints are not yet supported by the flatzinc backend.");
}

template<typename Stream>
void FlatZincRewriter<Stream>::visit(const InnerCPAllDiff&) {
	throw idpexception("Alldifferent is not yet supported by the flatzinc backend.");
}

// Explicit instantiations. Note, apparently, they have to be AT THE END of the cpp
template class FlatZincRewriter<std::ostream>;
