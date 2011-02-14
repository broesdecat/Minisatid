#include "modules/aggsolver/AggPrint.hpp"

#include "modules/aggsolver/AggProp.hpp"
#include "modules/aggsolver/PartiallyWatched.hpp"
#include "modules/AggSolver.hpp"

#include "utils/Print.hpp"

using namespace MinisatID;
using namespace MinisatID::Print;

void Aggrs::setAdded(){

}

void Aggrs::aggrAdded(){

}

void Aggrs::litPropagated(){

}

void Aggrs::explanationGenerated(){

}

void Aggrs::sets(){

}

void Aggrs::printWatches(int verbosity, AggSolver const * const solver, const std::vector<std::vector<Watch*> >& tempwatches){
	if(verbosity<10){
		return;
	}
	report("Current effective watches: \n");
	for(vsize i=0; i<2*solver->nVars(); i++){
		bool found = false;
		for(vsize j=0; !found && j<tempwatches[i].size(); j++){
			for(vsize k=0; !found && k<tempwatches[i][j]->getSet()->getAgg().size(); k++){
				GenPWatch* watch2 = dynamic_cast<GenPWatch*>(tempwatches[i][j]);
				if(watch2!=NULL && watch2->isInWS()){
					found = true;
				}
			}
		}

		if(!found){
			continue;
		}

		report("    Watch "); Print::print(toLit(i)); report(" used by: \n");
		for(vsize j=0; j<tempwatches[i].size(); j++){
			for(vsize k=0; k<tempwatches[i][j]->getSet()->getAgg().size(); k++){
				GenPWatch* watch2 = dynamic_cast<GenPWatch*>(tempwatches[i][j]);
				if(watch2!=NULL && watch2->isInWS()){
					report("        ");
					print(verbosity, *tempwatches[i][j]->getSet()->getAgg()[k], true);
				}
			}
		}
	}
	report("\n");
}

void Aggrs::print(int verbosity, const TypedSet& c, bool endl) {
	if(verbosity<7){
		report("set %d", c.getSetID());
	}else{
		report("set %d = { ", c.getSetID());
		bool begin = true;
		for (vwl::const_iterator i = c.getWL().begin(); i < c.getWL().end(); ++i) {
			if(!begin){
				report(", ");
			}
			begin = false;
			Print::print((*i).getLit());
			lbool value = c.getSolver()->value((*i).getLit());
			report("(%s)", value==l_Undef?"X":value==l_True?"T":"F");
			report("=%s", toString((*i).getWeight()).c_str());
		}
		report(" }, KB=%s", toString(c.getKnownBound()).c_str());
	}
	if (endl) {
		report("\n");
	}
}

void Aggrs::print(int verbosity, const Agg& ae, bool endl) {
	Print::print(ae.getHead());
	lbool value = ae.getSet()->getSolver()->value(ae.getHead());
	report("(%s)" , value==l_Undef?"X":value==l_True?"T":"F");
	TypedSet* set = ae.getSet();
	switch(ae.getSem()){
		case DEF:
			report("%s ", "<-");
			break;
		case COMP:
			report("%s ", "<=>");
			break;
		case IMPLICATION:
			report("%s ", "|");
			break;
	}
	if (ae.hasLB()) {
		report("%s <= ", toString(ae.getCertainBound()).c_str());
	}
	report("%s{", ae.getType()==MAX?"MAX":ae.getType()==MIN?"MIN":ae.getType()==SUM?"SUM":ae.getType()==CARD?"CARD":"PROD");
	print(verbosity, *set, false);
	report("}");
	if (ae.hasUB()) {
		report(" <= %s", toString(ae.getCertainBound()).c_str());
	}
	report(".");
	if(endl){
		report("\n");
	}
}
