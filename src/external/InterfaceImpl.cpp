#include "external/InterfaceImpl.hpp"

#include "external/Translator.hpp"

#include <cstdlib>
#include <vector>
#include <tr1/memory>
#include <algorithm>

#include "parser/ResourceManager.hpp"
#include "utils/PrintMessage.hpp"

using namespace std;
using namespace MinisatID;
using namespace MinisatID::Print;

///////
// REMAPPER
///////

Var Remapper::getVar(const Atom& atom){
	if(atom.getValue()<1){
		throw idpexception("Variables can only be numbered starting from 1.\n");
	}
	if(atom.getValue()>maxnumber){
		maxnumber = atom.getValue();
	}
	return atom.getValue()-1;
}

Literal Remapper::getLiteral(const Lit& lit){
	return Literal(var(lit)+1, sign(lit));
}

Var SmartRemapper::getVar(const Atom& atom){
	if(atom.getValue()<1){
		throw idpexception("Variables can only be numbered starting from 1.\n");
	}
	atommap::const_iterator i = origtocontiguousatommapper.find(atom.getValue());
	Var v = 0;
	if(i==origtocontiguousatommapper.end()){
		origtocontiguousatommapper.insert(pair<int, int>(atom.getValue(), maxnumber));
		contiguoustoorigatommapper.insert(pair<int, int>(maxnumber, atom.getValue()));
		v = maxnumber++;
		//report("Mapped %d to %d\n", atom.getValue(), v);
	}else{
		v = (*i).second;
	}
	return v;
}

Literal SmartRemapper::getLiteral(const Lit& lit){
	atommap::const_iterator atom = contiguoustoorigatommapper.find(var(lit));
	assert(atom!=contiguoustoorigatommapper.end());
	int origatom = (*atom).second;
	//report("Retrieved %d from %d\n", var(lit), origatom);
	return Literal(origatom, sign(lit));
}

///////
// IMPL
///////

WLSImpl::WLSImpl(const SolverOption& modes):
		_state(INIT), _modes(modes),
		_remapper(modes.remap?new SmartRemapper():new Remapper()),
		_translator(new Translator()), //Load with default translator
		firstmodel(true){
}

WLSImpl::~WLSImpl(){
	if(_translator!=NULL){
		delete _translator;
	}
	delete _remapper;
}

void WLSImpl::setTranslator(Translator* translator){
	_translator = translator;
}

void WLSImpl::printLiteral(std::ostream& output, const Lit& l) const{
	getTranslator()->printLiteral(output, getRemapper()->getLiteral(l));
}

void WLSImpl::printStatistics() const {
	getSolver()->printStatistics();
}

std::streambuf* WLSImpl::getRes() const {
	return getOutputBuffer();
}

Var WLSImpl::checkAtom(const Atom& atom){
	return getRemapper()->getVar(atom);
}

Lit WLSImpl::checkLit(const Literal& lit){
	return mkLit(checkAtom(lit.getAtom()), lit.hasSign());
}

void WLSImpl::checkLits(const vector<Literal>& lits, vec<Lit>& ll){
	for(vector<Literal>::const_iterator i=lits.begin(); i<lits.end(); i++){
		ll.push(checkLit(*i));
	}
}

void WLSImpl::checkLits(const vector<Literal>& lits, vector<Lit>& ll){
	for(vector<Literal>::const_iterator i=lits.begin(); i<lits.end(); i++){
		ll.push_back(checkLit(*i));
	}
}

void WLSImpl::checkAtoms(const vector<Atom>& atoms, vector<Var>& ll){
	for(vector<Atom>::const_iterator i=atoms.begin(); i<atoms.end(); i++){
		ll.push_back(checkAtom(*i));
	}
}

void WPCLSImpl::addForcedChoices(const vector<Literal> lits){
	vec<Lit> ll;
	checkLits(lits, ll);
	getSolver()->addForcedChoices(ll);
}

bool WLSImpl::finishParsing(){
	printInitDataStart(modes().verbosity);

	bool present = true, unsat = false;
	double cpu_time = cpuTime(); //Start time
	getSolver()->finishParsing(present, unsat);
	_state = PARSED;

	printInitDataEnd(modes().verbosity, cpuTime()-cpu_time, unsat);

	return !unsat;
}

bool WLSImpl::simplify(){
	printSimpStart(modes().verbosity);

	bool unsat = !getSolver()->simplify();
	_state = SIMPLIFIED;

	printSimpEnd(modes().verbosity, unsat);

	return !unsat;
}

bool WLSImpl::solve(Solution* sol){
	bool unsat = false;
	//Adding safety for interface users
	if(!unsat && _state==INIT){
		unsat = !finishParsing();
	}
	if(!unsat && _state==PARSED){
		unsat = !simplify();
	}
	if(unsat){
		return false;
	}

	assert(_state==SIMPLIFIED);
	printSolveStart(modes().verbosity);

	// Map to internal repr for assumptions
	vec<Lit> assumptions;
	checkLits(sol->getAssumptions(), assumptions);
	bool sat = getSolver()->solve(assumptions, sol);

	if(sol->getSearch()){
		_state = SOLVED;
	}

	printSolveEnd(modes().verbosity);

	return sat;
}

void WLSImpl::addModel(const vec<Lit>& model, Solution* sol){
	//Translate into original vocabulary
	vector<Literal> outmodel;
	for(int j=0; j<model.size(); j++){
		if(!getRemapper()->wasInput(var(model[j]))){ //was not part of the input
			continue;
		}
		outmodel.push_back(getRemapper()->getLiteral(model[j]));
	}
	sort(outmodel.begin(), outmodel.end());

	if(verbosity()>=5){
		report("Trimmed, remapped model: ");
		for(vector<Literal>::const_iterator i=outmodel.begin(); i<outmodel.end(); i++){
			report("%d ", (*i).getValue());
		}
		report("\n");
	}

	assert(sol!=NULL);
	sol->addModel(outmodel);

	if(sol->getPrint()){
		std::ostream output(getRes());
		if(sol->getNbModelsFound()==1){	//First model found
			output << "SAT\n";
			if(modes().verbosity>=1){
				report("SATISFIABLE\n");
			}
			getTranslator()->printHeader(output);
		}

		if(verbosity()>=1){
			report("> %4d model%s found\n",
					sol->getNbModelsFound(), sol->getNbModelsFound() > 1 ? "s" : " ");
		}

		//Effectively print the model
		getTranslator()->printModel(output, outmodel);
	}
}

///////
// PROP SOLVER
 ///////

WPCLSImpl::WPCLSImpl(const SolverOption& modes)
		:WLSImpl(modes), solver(new PCSolver(modes, this)){
}

WPCLSImpl::~WPCLSImpl(){
	delete solver;
}

PCSolver* WPCLSImpl::getSolver() const { return solver; }

void WPCLSImpl::addVar(Atom v){
	Var newv = checkAtom(v);
	getSolver()->addVar(newv);
}

bool WPCLSImpl::addClause(vector<Literal>& lits){
	vec<Lit> ll;
	checkLits(lits, ll);
	return getSolver()->addClause(ll);
}

bool WPCLSImpl::addEquivalence(const Literal& head, const vector<Literal>& body, bool conj){
	Lit h = checkLit(head);
	vec<Lit> b;
	checkLits(body, b);
	return getSolver()->addEquivalence(h, b, conj);
}

bool WPCLSImpl::addRule(bool conj, Literal head, const vector<Literal>& lits){
	Lit newhead = checkLit(head);
	vec<Lit> ll;
	checkLits(lits, ll);
	return getSolver()->addRule(conj, newhead, ll);
}

bool WPCLSImpl::addSet(int id, const vector<Literal>& lits){
	vec<Lit> ll;
	checkLits(lits, ll);
	return getSolver()->addSet(id, ll);
}

//Might be implemented more efficiently in the future
bool WPCLSImpl::addSet(int id, const vector<WLtuple>& lws){
	vector<Literal> lits;
	vector<Weight> weights;

	for(vector<WLtuple>::const_iterator i=lws.begin(); i<lws.end(); i++){
		lits.push_back((*i).l);
		weights.push_back((*i).w);
	}

	return addSet(id, lits, weights);
}

bool WPCLSImpl::addSet(int id, const vector<Literal>& lits, const vector<Weight>& w){
	vec<Lit> ll;
	checkLits(lits, ll);
	return getSolver()->addSet(id, ll, w);
}

bool WPCLSImpl::addAggrExpr(Literal head, int setid, const Weight& bound, AggSign sign, AggType type, AggSem sem){
	return getSolver()->addAggrExpr(checkLit(head), setid, bound, sign, type, sem);
}

bool WPCLSImpl::addMinimize(const vector<Literal>& lits, bool subsetmnmz){
	vec<Lit> ll;
	checkLits(lits, ll);
	return getSolver()->addMinimize(ll, subsetmnmz);
}

bool WPCLSImpl::addSumMinimize(const Atom head, const int setid){
    return getSolver()->addSumMinimize(checkAtom(head), setid);
}

bool WPCLSImpl::addIntVar(int groundname, int min, int max){
	return getSolver()->addIntVar(groundname, min, max);
}

bool WPCLSImpl::addCPBinaryRel(Literal head, int groundname, EqType rel, int bound){
	return getSolver()->addCPBinaryRel(checkLit(head), groundname, rel, bound);
}

bool WPCLSImpl::addCPBinaryRelVar(Literal head, int groundname, EqType rel, int groundname2){
	return getSolver()->addCPBinaryRelVar(checkLit(head), groundname, rel, groundname2);
}

bool WPCLSImpl::addCPSum(Literal head, const vector<int>& termnames, EqType rel, int bound){
	return getSolver()->addCPSum(checkLit(head), termnames, rel, bound);
}

bool WPCLSImpl::addCPSum(Literal head, const vector<int>& termnames, vector<int> mult, EqType rel, int bound){
	return getSolver()->addCPSum(checkLit(head), termnames, mult, rel, bound);
}

bool WPCLSImpl::addCPSumVar(Literal head, const vector<int>& termnames, EqType rel, int rhstermname){
	return getSolver()->addCPSum(checkLit(head), termnames, rel, rhstermname);
}

bool WPCLSImpl::addCPSumVar(Literal head, const vector<int>& termnames, vector<int> mult, EqType rel, int rhstermname){
	return getSolver()->addCPSum(checkLit(head), termnames, mult, rel, rhstermname);
}

bool WPCLSImpl::addCPCount(const vector<int>& termnames, int value, EqType rel, int rhstermname){
	return getSolver()->addCPCount(termnames, value, rel, rhstermname);
}

bool WPCLSImpl::addCPAlldifferent(const vector<int>& termnames){
	return getSolver()->addCPAlldifferent(termnames);
}

///////
// MODEL SOLVER
///////

WSOLSImpl::WSOLSImpl(const SolverOption& modes):
		WLSImpl(modes), solver(new SOSolver(modes, this)){
}

WSOLSImpl::~WSOLSImpl(){
	delete solver;
}

SOSolver* WSOLSImpl::getSolver() const { return solver; }

void WSOLSImpl::addVar(vsize modid, Atom v){
	getSolver()->addVar(modid, checkAtom(v));
}

bool WSOLSImpl::addClause(vsize modid, vector<Literal>& lits){
	vec<Lit> ll;
	checkLits(lits, ll);
	return getSolver()->addClause(modid, ll);
}

bool WSOLSImpl::addRule(vsize modid, bool conj, Literal head, vector<Literal>& lits){
	vec<Lit> ll;
	checkLits(lits, ll);
	return getSolver()->addRule(modid, conj, checkLit(head), ll);
}

bool WSOLSImpl::addSet(vsize modid, int id, vector<Literal>& lits, vector<Weight>& w){
	vec<Lit> ll;
	checkLits(lits, ll);
	return getSolver()->addSet(modid, id, ll, w);
}

//Might be implemented more efficiently in the future
bool WSOLSImpl::addSet(vsize modid, int id, vector<WLtuple>& lws){
	vector<Literal> lits;
	vector<Weight> weights;

	for(vector<WLtuple>::const_iterator i=lws.begin(); i<lws.end(); i++){
		lits.push_back((*i).l);
		weights.push_back((*i).w);
	}

	vec<Lit> ll;
	checkLits(lits, ll);

	return addSet(modid, id, lits, weights);
}

bool WSOLSImpl::addAggrExpr(vsize modid, Literal head, int setid, const Weight& bound, AggSign sign, AggType type, AggSem sem){
	return getSolver()->addAggrExpr(modid, checkLit(head), setid, bound, sign, type, sem);
}

//Add information for hierarchy
bool WSOLSImpl::addChild(vsize parent, vsize child, Literal head){
	return getSolver()->addChild(parent, child, checkLit(head));
}

bool WSOLSImpl::addAtoms(vsize modid, const vector<Atom>& atoms){
	vector<Var> aa;
	checkAtoms(atoms, aa);
	return getSolver()->addAtoms(modid, aa);
}
