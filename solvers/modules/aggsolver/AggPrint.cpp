#include "modules/aggsolver/AggPrint.hpp"

#include "modules/aggsolver/AggProp.hpp"
#include "modules/AggSolver.hpp"

using namespace MinisatID;

void Aggrs::print(const TypedSet& c, bool endl) {
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
	if (endl) {
		report(" }\n");
	} else {
		report(" }");
	}
}

void Aggrs::print(const Agg& ae, bool endl) {
	gprintLit(ae.getHead());
	lbool value = ae.getSet()->getSolver()->value(ae.getHead());
	report("(%s)", value==l_Undef?"X":value==l_True?"T":"F");
	TypedSet* set = ae.getSet();
	if (ae.hasUB()) {
		report(" <- ");
	} else {
		report(" <- %s <= ", toString(ae.getBound().lb).c_str());
	}
	report("%s{", ae.getType()==MAX?"MAX":ae.getType()==MIN?"MIN":ae.getType()==SUM?"SUM":ae.getType()==CARD?"CARD":"PROD");
	print(*set, false);
	if (ae.hasUB()) {
		report(" <= %s, ", toString(ae.getBound().ub).c_str());
	} else {
		report(", ");
	}
	report("ESV = %d.", toString(set->getESV()).c_str());
	if(endl){
		report("\n");
	}
}
