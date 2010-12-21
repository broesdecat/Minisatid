#include "modules/aggsolver/AggPrint.hpp"

#include "modules/aggsolver/AggProp.hpp"
#include "modules/AggSolver.hpp"

using namespace MinisatID;

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

void Aggrs::print(int verbosity, const TypedSet& c, bool endl) {
	if(verbosity<8){
		report("set %d", c.getSetID());
	}else{
		report("set %d = { ", c.getSetID());
		bool begin = true;
		for (vwl::const_iterator i = c.getWL().begin(); i < c.getWL().end(); ++i) {
			if(!begin){
				report(", ");
			}
			begin = false;
			gprintLit((*i).getLit());
			lbool value = c.getSolver()->value((*i).getLit());
			report("(%s)", value==l_Undef?"X":value==l_True?"T":"F");
			report("=%s", toString((*i).getWeight()).c_str());
		}
		report(" }");
	}
	if (endl) {
		report("\n");
	}
}

void Aggrs::print(int verbosity, const Agg& ae, bool endl) {
	gprintLit(ae.getHead());
	lbool value = ae.getSet()->getSolver()->value(ae.getHead());
	report("(%s)", value==l_Undef?"X":value==l_True?"T":"F");
	TypedSet* set = ae.getSet();
	if (ae.hasUB()) {
		report(" %s ", ae.isDefined()?"<-":"<=>");
	} else {
		report(" %s %s <= ", ae.isDefined()?"<-":"<=>", toString(ae.getCertainBound()).c_str());
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
