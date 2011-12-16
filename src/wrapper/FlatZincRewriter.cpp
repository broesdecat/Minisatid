/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#include "external/FlatZincRewriter.hpp"

#include <cstdlib>
#include <vector>
#include <algorithm>

#include "external/ResourceManager.hpp"
#include "external/Translator.hpp"

using namespace std;
using namespace MinisatID;

/**
 * TODO add support for constructs not present in Flatzinc
 * 		minimum, maximum and product optimization
 * 		subset minimization support
 * 		count and alldiff (peter will have transformations for these)
 * 		recursively defined aggregates
 */

FlatZincRewriter::FlatZincRewriter(const SolverOption& modes):
		state(PARSING),
		_modes(modes),
		maxatomnumber(0),
		maxcpnumber(0),
		optim(MNMZ_NONE)
		{
}

FlatZincRewriter::~FlatZincRewriter(){
}

std::ostream& FlatZincRewriter::getOutput(){
	return std::cout;
}

const WSet& FlatZincRewriter::getSet(uint i) const {
	if(sets.size()<=i){
		throw idpexception("One of the aggregate sets was not declared before use.");
	}
	return sets[i];
}

//INVARIANT: always have already done a "check" operation on the atom
string getVarName(const Atom& atom){
	stringstream ss;
	ss <<"BOOL____" <<atom.getValue();
	return ss.str();
}

string getVarName(const Literal& lit){
	int value = lit.getAtom().getValue();
	stringstream ss;
	if(lit.hasSign()){
		ss <<"BOOL_NEG" <<value;
	}else{
		ss <<getVarName(lit.getAtom());
	}
	return ss.str();
}

string getVarName(int cpvar){
	stringstream ss;
	ss <<"INT__" <<cpvar;
	return ss.str();
}

string getIntVarName(const Literal& lit){
	int value = lit.getAtom().getValue();
	stringstream ss;
	if(lit.hasSign()){
		ss <<"INT_BOOL_" <<value;
	}else{
		ss <<"INT_BOOL_NEG_" <<value;
	}

	return ss.str();
}

void addDefAnnotation(int defID, ostream& stream){
	stream <<"::inductivelydefined(" <<defID <<")";
}

template<>
void FlatZincRewriter::check(const Atom& atom){
	check(Literal(atom, false));
}

//INVARIANT: for a negative literal, a bool var representing the positive literal and an equivalence constraint will ALWAYS be added
template<>
void FlatZincRewriter::check(const Literal& lit){
	int value = lit.getAtom().getValue();
	set<uint>& seenset = lit.hasSign()?negatomsseen:atomsseen;

	bool add = false;
	if(seenset.find(value)==seenset.cend()){
		seenset.insert(value);
		add = true;
	}

	if(add){
		if(maxatomnumber<std::abs(value)){
			maxatomnumber = value;
		}

		definitions <<"var bool: " <<getVarName(lit);
		if(isParsing()){
			definitions <<"::output_var";
		}
		definitions <<";\n";

		if(lit.hasSign()){ //also create positive one and add constraint (see invar)
			Literal poslit = Literal(value, false);
			check(poslit);
			constraints <<"constraint bool_not(" <<getVarName(lit) <<", " <<getVarName(~lit) <<");\n";
		}
	}
}

// Allows to add integer representation only once
void FlatZincRewriter::createIntVar(const Literal& lit, bool def, int defID){
	int value = lit.getAtom().getValue();
	set<uint>& seenset = lit.hasSign()?litnegatomsseen:litatomsseen;

	if(seenset.find(value)==seenset.cend()){
		seenset.insert(value);
		definitions <<"var 0..1: " <<getIntVarName(lit) <<";\n";
		constraints <<"constraint int_eq_reif(" <<getIntVarName(lit) <<", " <<"1" <<", " <<getVarName(lit) <<")";
		if(def){
			addDefAnnotation(defID, constraints);
		}
		constraints <<";\n";
	}
}

const Weight& FlatZincRewriter::getMin(uint var){
	assert(varbounds.find(var)!=varbounds.cend());
	return (*varbounds.find(var)).second.first;
}

const Weight& FlatZincRewriter::getMax(uint var){
	assert(varbounds.find(var)!=varbounds.cend());
	return (*varbounds.find(var)).second.second;
}

template<>
void FlatZincRewriter::check(const vector<Literal>& lits){
	for(vector<Literal>::const_iterator i=lits.cbegin(); i<lits.cend(); ++i){
		check(*i);
	}
}

template<>
void FlatZincRewriter::checkOnlyPos(const vector<Literal>& lits){
	for(vector<Literal>::const_iterator i=lits.cbegin(); i<lits.cend(); ++i){
		check((*i).getAtom());
	}
}

template<typename T>
void addMappedList(const vector<T>& list, ostream& stream){
	bool begin = true;
	for(typename vector<T>::const_iterator i=list.cbegin(); i<list.cend(); ++i){
		if(!begin){
			stream <<", ";
		}
		begin = false;
		stream <<getVarName(*i);
	}
}

template<typename T>
void addIntVarList(const vector<T>& list, ostream& stream){
	bool begin = true;
	for(typename vector<T>::const_iterator i=list.cbegin(); i<list.cend(); ++i){
		if(!begin){
			stream <<", ";
		}
		begin = false;
		stream <<getIntVarName(*i);
	}
}

template<typename T>
void addIntList(const vector<T>& list, ostream& stream){
	bool begin = true;
	for(typename vector<T>::const_iterator i=list.cbegin(); i<list.cend(); ++i){
		if(!begin){
			stream <<", ";
		}
		begin = false;
		stream <<*i;
	}
}

void FlatZincRewriter::printRel(const string& left, const string& right, const Literal& head, const string& constr){
	constraints <<"constraint " <<constr <<"(" <<left <<", " <<right <<", " <<getVarName(head) <<");\n";
}

void FlatZincRewriter::addBinRel(const string& left, const string& right, const Literal& head, EqType rel){
	string constr;
	Literal h = head;
	switch(rel){
	case MEQ:
		constr = "int_eq_reif";
		break;
	case MNEQ:
		constr = "int_ne_reif";
		break;
	case ML:
		constr = "int_lt_reif";
		break;
	case MG:{
		h = ~head;
		constr = "int_le_reif";
		break;}
	case MGEQ:{
		h = ~head;
		constr = "int_lt_reif";
		break;}
	case MLEQ:
		constr = "int_le_reif";
		break;
	}
	check(h);
	printRel(left,right, h, constr);
}


void FlatZincRewriter::printSum(const weightlist& weights, const string& vars, const Atom& head, string constr, string bound){
	constraints <<"constraint " <<constr <<"([";
	addIntList(weights, constraints);
	constraints <<"],[" <<vars <<"], " <<bound <<", " <<getVarName(head) <<");\n";
}

Atom FlatZincRewriter::createAtom(){
	Atom lit = Atom(maxatomnumber+1);
	check(lit);
	return lit;
}

void FlatZincRewriter::addSum(const weightlist& weights, const vector<uint>& vars, const Atom& head, EqType rel, const Weight& bound){
	stringstream ss;
	bool begin = true;
	for(vector<uint>::const_iterator i=vars.cbegin(); i<vars.cend(); ++i){
		if(!begin){
			ss <<", ";
		}
		begin = false;
		ss <<getVarName(*i);
	}
	addSum(weights, ss.str(), head, rel, bound);
}

void FlatZincRewriter::addSum(const weightlist& weights, const string& vars, const Atom& head, EqType rel, const Weight& bound){
	string constr = "";
	Weight newbound = bound;
	switch(rel){
	case MEQ:
		constr = "int_lin_eq_reif";
		break;
	case MNEQ:
		constr = "int_lin_ne_reif";
		break;
	case ML:
		constr = "int_lin_le_reif";
		newbound = bound-1;
		break;
	case MG:{
		Atom newhead = createAtom();
		constr = "int_lin_le_reif";
		constraints <<"constraint bool_not(" <<getVarName(head) <<", " <<getVarName(newhead) <<");\n";
		break;}
	case MGEQ:{
		Atom newhead = createAtom();
		constr = "int_lin_le_reif";
		newbound = bound-1;
		constraints <<"constraint bool_not(" <<getVarName(head) <<", " <<getVarName(newhead) <<");\n";
		break;}
	case MLEQ:
		constr = "int_lin_le_reif";
		break;
	}

	stringstream ss;
	ss <<newbound;

	printSum(weights, vars, head, constr, ss.str());
}

void FlatZincRewriter::addVarSum(const weightlist& weights, const vector<uint>& vars, const Atom& head, EqType rel, uint rhsvar){
	vector<uint> newvars = vars;
	newvars.push_back(rhsvar);

	weightlist newweights = weights;
	newweights.push_back(-1);

	addSum(newweights, newvars, head, rel, 0);
}

void FlatZincRewriter::addVarSum(const weightlist& weights, const vector<Literal>& lits, const Atom& head, EqType rel, uint rhsvar){
	stringstream ss;
	bool begin = true;
	for(vector<Literal>::const_iterator i=lits.cbegin(); i<lits.cend(); ++i){
		if(!begin){
			ss <<", ";
		}
		begin = false;
		ss <<getIntVarName(*i);
	}

	ss <<", " <<getVarName(rhsvar);
	weightlist newweights = weights;
	newweights.push_back(-1);

	addSum(newweights, ss.str(), head, rel, 0);
}

void FlatZincRewriter::addSum(const Aggregate& agg, const WSet& set){
	for(literallist::const_iterator i=set.literals.cbegin(); i<set.literals.cend(); ++i){
		createIntVar(*i, agg.sem==DEF, agg.defID);
	}

	Literal h = Literal(agg.head, false);
	Weight bound = agg.bound;
	if(agg.sign==AGGSIGN_LB){ // Have to swap the sign, by adding the negated head and reducing bound
		h = Literal(agg.head, true);
		check(h);
		bound -= 1;
	}

	// add the constraint
	constraints <<"constraint int_lin_le_reif([";
	addIntList(set.weights, constraints);
	constraints <<"], [";
	addIntVarList(set.literals, constraints);
	constraints <<"], " <<bound <<", " <<getVarName(h) <<");\n";
}

uint FlatZincRewriter::createCpVar(const Weight& min, const Weight& max){
	CPIntVarRange newvar;
	newvar.varID = maxcpnumber+1;
	newvar.minvalue = min;
	newvar.maxvalue = max;
	add(newvar);
	return newvar.varID;
}

uint FlatZincRewriter::createCpVar(const std::vector<Weight>& values){
	CPIntVarEnum newvar;
	newvar.varID = maxcpnumber+1;
	newvar.values = values;
	add(newvar);
	return newvar.varID;
}

uint FlatZincRewriter::addOptimization(){
	int optimvar = 0;
	if(optim==MNMZ_AGG){
		const MinimizeAgg& mnm = savedagg;
		if(mnm.type != SUM && mnm.type != CARD){
			throw idpexception("Optimization only supported on sum or cardinality aggregates.");
		}
		const WSet& set = getSet(mnm.setid);
		Weight min = 0, max = 0;
		for(weightlist::const_iterator i=set.weights.cbegin(); i<set.weights.cend(); ++i){
			if((*i)<0){
				min += *i;
			}else{
				max += *i;
			}
		}

		optimvar = createCpVar(min, max);

		for(literallist::const_iterator i=set.literals.cbegin(); i<set.literals.cend(); ++i){
			createIntVar(*i, false, 0);
		}

		addVarSum(set.weights, set.literals, mnm.head, MEQ, optimvar);
		Disjunction d;
		d.literals.push_back(Literal(mnm.head));
		add(d);
	}else if(optim==MNMZ_LIST){
		const MinimizeOrderedList& mnm = savedlistmnmz;

		optimvar = createCpVar(1, long(mnm.literals.size()));

		int currentvalue = 1;
		for(literallist::const_iterator i=mnm.literals.cbegin(); i<mnm.literals.cend(); ++i){
			stringstream ss;
			ss <<currentvalue;
			addBinRel(getVarName(optimvar), ss.str(), *i, MEQ);
			currentvalue++;
		}
	}else if(optim==MNMZ_SUBSET){
		throw idpexception("Subset minimization is not supported by the FlatZinc language.");
	}else{
		assert(optim==MNMZ_VAR);
		// TODO
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
void FlatZincRewriter::addProduct(const Aggregate& agg, const WSet& set){
	bool begin = true;
	Weight min = 1, max = 1;
	uint prevvar = 0;
	for(uint i=0; i<set.literals.size(); ++i){
		const Weight& weight = set.weights[i];

		if(weight==1){ // FIXME ugly hack to prevent problems with the equivalence of the intvar with the maxvalue (preventing the bool var to become false)
			continue;
		}

		vector<Weight> weights;
		weights.push_back(1);
		weights.push_back(weight);

		uint varID = createCpVar(weights);
		constraints <<"constraint int_eq_reif(" <<getVarName(varID) <<", " <<weight <<", " <<getVarName(set.literals[i]) <<");\n";

		Weight prevmin = min;
		Weight prevmax = max;
		min = std::min(min, weight*prevmin);
		min = std::min(min, weight*prevmax);
		max = std::max(max, weight*prevmin);
		max = std::max(max, weight*prevmax);

		if(!begin){
			uint newvar = createCpVar(min, max);
			constraints <<"constraint int_times(" <<getVarName(varID) <<", " <<getVarName(prevvar) <<", " <<getVarName(newvar) <<");\n";
			prevvar = newvar;
		}else{
			prevvar = varID;
		}
		begin = false;
	}

	stringstream ss;
	ss <<agg.bound;
	addBinRel(getVarName(prevvar), ss.str(), Literal(agg.head, false), agg.sign==AGGSIGN_LB?MGEQ:MLEQ);
}

void FlatZincRewriter::finishParsing(){
	state = FINISHING;

	for(vector<BinRel>::const_iterator i=savedbinrels.cbegin(); i<savedbinrels.cend(); ++i){
		addBinRel((*i).left, (*i).right, Literal((*i).head, false), (*i).rel);
	}

	for(vector<CPSumWeighted>::const_iterator i=savedcpsums.cbegin(); i<savedcpsums.cend(); ++i){
		addSum((*i).weights, (*i).varIDs, (*i).head, (*i).rel, (*i).bound);
	}

	for(vector<Aggregate>::const_iterator i=savedaggs.cbegin(); i<savedaggs.cend(); ++i){
		if((*i).type==PROD){
			addProduct(*i, getSet((*i).setID));
		}else{
			assert((*i).type==SUM || (*i).type==CARD);
			addSum(*i, getSet((*i).setID));
		}
	}

	uint optimvar = addOptimization();

	getOutput() <<definitions.str();
	getOutput() <<constraints.str();
	if(optim!=MNMZ_NONE){
		getOutput() <<"solve minimize " <<getVarName(optimvar) <<";\n";
	}else{
		getOutput() <<"solve satisfy;\n";
	}
}

// ADDITION METHODS

void FlatZincRewriter::addIntegerVar(uint varID, const string& domainexpr, const Weight& min, const Weight& max){
	if(cpvarsseen.find(varID)!=cpvarsseen.cend()){
		stringstream ss;
		ss <<"Double addition of integer variable " <<varID <<".";
		throw idpexception(ss.str());
	}

	definitions <<"var " <<domainexpr <<": " <<getVarName(varID);
	if(isParsing()){
		definitions <<"::output_var";
	}
	definitions <<";\n";

	cpvarsseen.insert(varID);
	varbounds.insert(pair<uint, pair<Weight, Weight> >(varID, pair<Weight, Weight>(min, max)));
	if(maxcpnumber<varID){
		maxcpnumber = varID;
	}
}

void FlatZincRewriter::addEquiv(const Literal& head, const literallist& body, bool conjunctive, CloseConstraint close){
	check(body);
	check(head);

	if(conjunctive){
		constraints <<"constraint array_bool_and([";
	}else{
		constraints <<"constraint array_bool_or([";
	}
	addMappedList(body, constraints);
	constraints  <<"], " <<getVarName(head) <<")";
	if(close==CLOSE){
		constraints <<";\n";
	}
}

void FlatZincRewriter::add(const WSet& set, int setID){
	check(set.literals);
	sets.resize(setID+1);
	sets[setID] = set;
}

template<>
SATVAL FlatZincRewriter::add(const literallist& lits){
	literallist pos, neg;
	for(literallist::const_iterator i=lits.cbegin(); i<lits.cend(); ++i){
		if((*i).hasSign()){
			neg.push_back(~(*i));
		}else{
			pos.push_back(*i);
		}
	}

	check(pos);
	check(neg);

	constraints <<"constraint bool_clause([";
	addMappedList(pos, constraints);
	constraints <<"], [";
	addMappedList(neg, constraints);
	constraints  <<"]);\n";
	return SATVAL::POS_SAT;
}

template<>
SATVAL FlatZincRewriter::add(const Disjunction& sentence){
	add(sentence.literals);
	return SATVAL::POS_SAT;
}

template<>
SATVAL FlatZincRewriter::add(const DisjunctionRef& sentence){
	add(sentence.literals);
	return SATVAL::POS_SAT;
}

template<>
SATVAL FlatZincRewriter::add(const Equivalence& equiv){
	addEquiv(equiv.head, equiv.body, equiv.conjunctive, CLOSE);
	return SATVAL::POS_SAT;
}

template<>
SATVAL FlatZincRewriter::add(const Rule& rule){
	checkOnlyPos(rule.body);
	check(rule.head);

	if(!rule.conjunctive){
		if(rule.body.size()>1){
			SATVAL satpossible = SATVAL::POS_SAT;
			for(literallist::const_iterator i=rule.body.cbegin(); satpossible==SATVAL::POS_SAT && i<rule.body.cend(); ++i){
				Rule smallrule;
				smallrule.head = rule.head;
				smallrule.body.push_back(*i);
				smallrule.conjunctive = true;
				smallrule.definitionID = rule.definitionID;
				satpossible &= add(smallrule);
			}
			return satpossible;
		}else if(rule.body.size()==0){
			Disjunction clause;
			clause.literals.push_back(Literal(rule.head, true));
			return add(clause);
		}
	}

	constraints <<"constraint inductive_rule(";
	constraints <<getVarName(rule.head) <<", ";

	constraints <<"[";
	bool begin = true;
	for(literallist::const_iterator i=rule.body.cbegin(); i<rule.body.cend(); ++i){
		if((*i).hasSign()){
			continue;
		}
		if(!begin){
			constraints <<", ";
		}
		begin = false;
		constraints <<getVarName(*i);
	}
	constraints  <<"], ";

	constraints <<"[";
	begin = true;
	for(literallist::const_iterator i=rule.body.cbegin(); i<rule.body.cend(); ++i){
		if(!(*i).hasSign()){
			continue;
		}
		if(!begin){
			constraints <<", ";
		}
		begin = false;
		constraints <<getVarName(~*i);
	}
	constraints  <<"], ";

	constraints <<rule.definitionID;
	constraints <<");\n";
	return SATVAL::POS_SAT;
}

template<>
SATVAL FlatZincRewriter::add(const Set& set){
	WSet wset;
	for(literallist::const_iterator i=set.literals.cbegin(); i<set.literals.cend(); ++i){
		wset.literals.push_back(*i);
		wset.weights.push_back(1);
	}
	add(wset, set.setID);
	return SATVAL::POS_SAT;
}

template<>
SATVAL FlatZincRewriter::add(const WSet& set){
	add(set, set.setID);
	return SATVAL::POS_SAT;
}

template<>
SATVAL FlatZincRewriter::add(const WLSet& set){
	WSet wset;
	for(vector<WLtuple>::const_iterator i=set.wl.cbegin(); i<set.wl.cend(); ++i){
		wset.literals.push_back((*i).l);
		wset.weights.push_back((*i).w);
	}
	add(wset, set.setID);
	return SATVAL::POS_SAT;
}

template<>
SATVAL FlatZincRewriter::add(const Aggregate& origagg){
	check(origagg.head);

	if(origagg.type==PROD){
		assert(isParsing());
		savedaggs.push_back(origagg);
	}else if(origagg.type==CARD || origagg.type==SUM){
		assert(isParsing());
		savedaggs.push_back(origagg);
	}else{ // MIN or MAX
		Aggregate agg(origagg);
		WSet set = getSet(agg.setID);

		// Transform min into max
		if(agg.type==MIN){
			for (weightlist::size_type i = 0; i < set.weights.size(); ++i) {
				set.weights[i] = -set.weights[i];
			}

			agg.bound = -agg.bound;
			agg.sign = agg.sign==AGGSIGN_LB?AGGSIGN_UB:AGGSIGN_LB;
		}

		bool ub = agg.sign==AGGSIGN_UB;
		literallist lits;
		for (weightlist::size_type i = 0; i < set.weights.size(); i++) {
			if(set.weights[i] < agg.bound){
				continue;
			}
			if(ub && set.weights[i] == agg.bound){
				continue;
			}
			lits.push_back(ub?~set.literals[i]:set.literals[i]);
		}

		addEquiv(Literal(agg.head, false), lits, ub, OPEN);
		if(agg.sem==DEF){
			addDefAnnotation(agg.defID, constraints);
		}
		constraints <<";\n";
	}
	return SATVAL::POS_SAT;
}

template<>
SATVAL FlatZincRewriter::add(const MinimizeSubset& sentence){
	assert(isParsing());
	optim = MNMZ_SUBSET;
	savedsubsetmnmz = sentence;
	check(sentence.literals);
	return SATVAL::POS_SAT;
}

template<>
SATVAL FlatZincRewriter::add(const MinimizeOrderedList& sentence){
	assert(isParsing());
	optim = MNMZ_LIST;
	check(sentence.literals);
	savedlistmnmz = sentence;
	return SATVAL::POS_SAT;
}

template<>
SATVAL FlatZincRewriter::add(const MinimizeVar& mnm){
	assert(isParsing());
	savedvar = mnm;
	optim = MNMZ_VAR;
	return SATVAL::POS_SAT;
}

template<>
SATVAL FlatZincRewriter::add(const MinimizeAgg& mnm){
	assert(isParsing());
	savedagg = mnm;
	optim = MNMZ_AGG;
	return SATVAL::POS_SAT;
}

template<>
SATVAL FlatZincRewriter::add(const CPIntVarEnum& var){
	stringstream ss;
	ss <<"{";
	bool begin = true;
	for(vector<Weight>::const_iterator i=var.values.cbegin(); i<var.values.cend(); ++i){
		if(!begin){
			ss <<", ";
		}
		begin = false;
		ss <<*i;
	}
	ss <<"}";

	Weight min = var.values[0], max = var.values[0];
	for(uint i=1; i<var.values.size(); ++i){
		const Weight& w = var.values[i];
		if(w<min){
			min = w;
		}
		if(w > max){
			max = w;
		}
	}
	addIntegerVar(var.varID, ss.str(), min, max);
	return SATVAL::POS_SAT;
}

template<>
SATVAL FlatZincRewriter::add(const CPIntVarRange& var){
	stringstream ss;
	ss <<var.minvalue <<".." <<var.maxvalue;
	addIntegerVar(var.varID, ss.str(), var.minvalue, var.maxvalue);
	return SATVAL::POS_SAT;
}

template<>
SATVAL FlatZincRewriter::add(const CPBinaryRel& rel){
	assert(isParsing());
	check(rel.head);

	BinRel binrel;
	binrel.left = getVarName(rel.varID);
	stringstream ss;
	ss <<rel.bound;
	binrel.right = ss.str();
	binrel.head = rel.head;
	binrel.rel = rel.rel;
	savedbinrels.push_back(binrel);
	return SATVAL::POS_SAT;
}

template<>
SATVAL FlatZincRewriter::add(const CPBinaryRelVar& rel){
	assert(isParsing());
	check(rel.head);

	BinRel binrel;
	binrel.left = getVarName(rel.lhsvarID);
	binrel.right = getVarName(rel.rhsvarID);
	binrel.head = rel.head;
	binrel.rel = rel.rel;
	savedbinrels.push_back(binrel);
	return SATVAL::POS_SAT;
}

template<>
SATVAL FlatZincRewriter::add(const CPSumWeighted& sum){
	assert(isParsing());
	check(sum.head);
	savedcpsums.push_back(sum);
	return SATVAL::POS_SAT;
}

template<>
SATVAL FlatZincRewriter::add(const CPCount& sentence){
	throw idpexception("Count constraints are not yet supported by the flatzinc backend.");
}

template<>
SATVAL FlatZincRewriter::add(const CPAllDiff& sentence){
	throw idpexception("Alldifferent is not yet supported by the flatzinc backend.");
}
