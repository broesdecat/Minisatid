#include "Heuristics.hpp"
#include "satsolver/minisat/Solver.hpp"

using namespace std;
using namespace MinisatID;
using namespace Minisat;

MinisatHeuristic::MinisatHeuristic(bool rand_pol):var_inc(1),rnd_pol(rand_pol),order_heap(VarOrderLt(activity)){}

void MinisatHeuristic::addAtom(Atom v, lbool upol){
	activity.growTo(v+1,0);
	activity[v]=rnd_init_act ? S->getRandNumber() * 0.00001 : 0;
	occurrences.resize((v+1)*2,0);
	polarity.growTo(v+1,true);
	if(S->getPCSolver().modes().lazyheur){ // TODO: this
		polarity[v]=((float)rand()/ RAND_MAX)>0.2;
	}
	user_pol.growTo(v+1,l_Undef);
	user_pol[v]=upol;
}

Atom MinisatHeuristic::getNextVariable(){
	Atom next = var_Undef;

	// Random decision:
	if (S->getRandNumber() < random_var_freq && !order_heap.empty()) {
		next = order_heap[S->getRandInt(order_heap.size())];
		if (S->value(mkPosLit(next)) == l_Undef && S->decision[next]) {
			S->rnd_decisions++;
		}
	}

	// Activity based decision:
	while (next == var_Undef || S->value(mkPosLit(next)) != l_Undef || !S->decision[next]) {
		if (order_heap.empty()){
			next = var_Undef;
			break;
		}else{
			next = order_heap.removeMin();
		}
	}

	return next;
}

Lit MinisatHeuristic::choosePolarity(Atom next){
	// Choose polarity based on different polarity modes (global or per-variable):
	if (next == var_Undef) {
		return lit_Undef;
	} else if (user_pol[next] != l_Undef) {
		return mkLit(next, user_pol[next] == l_True);
	} else if (rnd_pol) {
		return mkLit(next, S->getRandNumber() < 0.5);
	} else {
		return mkLit(next, polarity[next]);
	}
}

void MinisatHeuristic::adjustPriority(Atom v, double inc){
	if ((activity[v] += inc) > 1e100) {
		// Rescale:
		for (int i = 0; i < S->nVars(); i++)
			activity[i] *= 1e-100;
		var_inc *= 1e-100;
	}

	// Update order_heap with respect to new activity:
	if (order_heap.inHeap(v))
		order_heap.decrease(v);
}

void MinisatHeuristic::IncreasePriority(Atom v){
	adjustPriority(v, var_inc);
}
void MinisatHeuristic::DecreasePriority(Atom v){
	adjustPriority(v, -var_inc);
}

void MinisatHeuristic::notifyRestart(){
	if(S->getNbOfRestarts()<1){
		for (Atom v = 0; v < S->nVars(); ++v) {
			activity[v]=occurrences.at(toInt(mkPosLit(v)))+occurrences.at(toInt(mkNegLit(v)));
			polarity[v]=occurrences.at(toInt(mkPosLit(v)))<=occurrences.at(toInt(mkNegLit(v)));
		}
		notifySimplification();
	}
}

void MinisatHeuristic::notifyNewClause(Minisat::Clause& clause){
	if(S->getNbOfRestarts()<1){
		for(int i=0; i<clause.size(); ++i){
			++occurrences[toInt(clause[i])];
		}
	}
}

void MinisatHeuristic::notifyRemoveClause(Minisat::Clause& clause){
	if(S->getNbOfRestarts()<1){
		for(int i=0; i<clause.size(); ++i){
			--occurrences[toInt(clause[i])];
		}
	}
}

void MinisatHeuristic::notifyConflict(std::vector<Lit>& conflictClause){
	for(auto l: conflictClause){
		IncreasePriority(var(l));
	}
}

void MinisatHeuristic::notifySimplification(){
	vec<Atom> vs;
	for (Atom v = 0; v < S->nVars(); v++) {
		if (S->decision[v] && S->value(mkPosLit(v)) == l_Undef)
			vs.push(v);
	}
	order_heap.build(vs);
}

void MinisatHeuristic::notifyBacktrack(Lit l, bool cBiggerThanTrailLimLast){
	if (phase_saving > 1 || (phase_saving == 1 && cBiggerThanTrailLimLast)) {
		polarity[var(l)] = sign(l);
	}

	if (!order_heap.inHeap(var(l)) && S->decision[var(l)])
		order_heap.insert(var(l));
}
void MinisatHeuristic::notifyOfLazyAtom(Atom vnew, Atom v1, Atom v2){
	double firstact = v1!=var_Undef?activity[v1]:0;
	double secondact = v2!=var_Undef?activity[v2]:0;
	double act = (firstact + secondact) / 2;
	adjustPriority(vnew, act-activity[vnew]);
}

void MinisatHeuristic::setPolarity(Atom var, bool makeTrue ){
	polarity[var] = not makeTrue;
}

void MinisatHeuristic::initialSetDecidable(Atom v){ // TODO: insert this in addAtom
	if (!order_heap.inHeap(v) && S->decision[v])
			order_heap.insert(v);
}

void MinisatHeuristic::notifyRandomizedRestart(std::vector<Atom>& affectedVars){
	for(auto decvar:affectedVars){
		if(S->getRandNumber()>0.6){
			polarity[decvar] = S->getRandNumber()>0.7?true:false;
		}
		if(S->getRandNumber()<0.4){
			DecreasePriority(decvar);
		}
	}
}

void MinisatHeuristic::notifyAggregate(Atom v){
	IncreasePriority(v);
}

void MinisatHeuristic::notifyAggPropInit(Atom v){
	IncreasePriority(v);
}

void MinisatHeuristic::notifyTypedSet(Atom v){
	IncreasePriority(v);
}

void MinisatHeuristic::notifyHead(Atom v){
	IncreasePriority(v);
}

VarMTF::VarMTF(int nrPushedLiterals):MinisatHeuristic(false),currentMax(0),nrPushedLits(nrPushedLiterals){}

void VarMTF::addAtom(Atom v, lbool upol){
	activity.growTo(v+1,0);
	occurrences.resize((v+1)*2,0);
	polarity.growTo(v+1,true);
	if(S->getPCSolver().modes().lazyheur){ // TODO: this
		polarity[v]=((float)rand()/ RAND_MAX)>0.2;
	}
	berkAct.resize(v+1,0);
}

Atom VarMTF::getNextVariable(){
	Atom next = var_Undef;

	while (next == var_Undef || S->value(mkPosLit(next)) != l_Undef || !S->decision[next]) {
		if (order_heap.empty()){
			next = var_Undef;
			break;
		}else{
			next = order_heap.removeMin();
		}
	}

	return next;
}

Lit VarMTF::choosePolarity(Atom next){
	if (next == var_Undef) {
		return lit_Undef;
	} else {
		return mkLit(next,polarity[next]);
	}
}

void VarMTF::pushToFront(Atom v){
	activity[v]=(++currentMax);
	if (currentMax >= 1e100) {
		// Rescale:
		for (int i = 0; i < S->nVars(); ++i){
			activity[i] *= 1e-100;}
		currentMax = 1;
	}

	// Update order_heap with respect to new activity:
	if (order_heap.inHeap(v)){
		order_heap.decrease(v);
	}

}

void VarMTF::notifyNewClause(Minisat::Clause& clause){
	for(int i=0; i<clause.size(); ++i){
		++occurrences[toInt(clause[i])];
	}
	// NOTE: originally, this was code in notifyConflict...
	if(clause.size()<nrPushedLits){
		for(int i=0; i<clause.size(); ++i){
			pushToFront(clause[i].getAtom());
		}
	}else{
		//printf("creating berk_order:\n");
		multimap<double,Lit> berk_order;
		for(int i=0; i<clause.size(); ++i){
			Lit tmp = clause[i];
			berk_order.insert({berkAct[var(tmp)],tmp});
			//printf("%i: %.1f\n",tmp.x,berkAct[var(tmp)]);
		}

		auto iter = berk_order.crbegin();
		for(int i=0; i<nrPushedLits; ++i){
			//printf("%i: %.1f\n",iter->second.x,berkAct[var(iter->second)]);
			pushToFront(iter->second.getAtom()); // TODO: do something about doubles
			iter++;
		}
	}
}

void VarMTF::notifyRemoveClause(Minisat::Clause& clause){
	for(int i=0; i<clause.size(); ++i){
		--occurrences[toInt(clause[i])];
	}
}

void VarMTF::notifyConflict(std::vector<Lit>& conflictClause){
	for(auto l: conflictClause){
		Atom v=var(l);
		if ((berkAct[v] += var_inc) > 1e100) {
			// Rescale:
			for (int i = 0; i < S->nVars(); i++)
				berkAct[i] *= 1e-100;
			var_inc *= 1e-100;
		}
	}
}

void VarMTF::notifyOfLazyAtom(Atom vnew, Atom v1, Atom v2){
	pushToFront(vnew);
}

void VarMTF::notifyRandomizedRestart(std::vector<Atom>& affectedVars){
	for(auto decvar:affectedVars){
		if(S->getRandNumber()>0.6){
			polarity[decvar] = S->getRandNumber()>0.7?true:false;
		}
	}
}

void VarMTF::notifyAggregate(Atom v){
	pushToFront(v);
}

void VarMTF::notifyAggPropInit(Atom v){
	pushToFront(v);
}

void VarMTF::notifyTypedSet(Atom v){
	pushToFront(v);
}

void VarMTF::notifyHead(Atom v){
	pushToFront(v);
}

void VarMTF::notifyRestart(){
	currentMax=-1;
	for (Atom v = 0; v < S->nVars(); ++v) {
		activity[v]=occurrences.at(toInt(mkPosLit(v)))+occurrences.at(toInt(mkNegLit(v)));
		if(activity[v]>currentMax){
			currentMax=(int)activity[v];
		}
		if(S->getNbOfRestarts()<1){
			polarity[v]=occurrences.at(toInt(mkPosLit(v)))<=occurrences.at(toInt(mkNegLit(v)));
		}
	}
	notifySimplification();
}
