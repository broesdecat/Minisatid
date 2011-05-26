/*
 * EventQueue.hpp
 *
 *  Created on: May 26, 2011
 *      Author: broes
 */

#ifndef EVENTQUEUE_HPP_
#define EVENTQUEUE_HPP_

class EventQueue {
public:
	EventQueue();
	virtual ~EventQueue();
	// IMPORTANT: implicit invariant that IDsolver is always last in the list!
	//operations

	//events
	//new decision level
	//backtrack
	//modelfound (wellfoundedness check)
	//branch choice
	//

	/*
	 * checkstatus
	//TODO use staged propagator for this
	if(status==l_True){ //Model found, check model:
		for(map<defID, WrappedPropagator*>::const_iterator i=idsolvers.begin(); i!=idsolvers.end(); ++i){
			if((*i).second->present && !dynamic_cast<IDSolver*>((*i).second->get())->checkStatus()){
				return l_False;
			}
		}

		if(hasPresentAggSolver() && !getAggSolver()->checkStatus()){
			return l_False;
		}
	}
	return status;*/
	/*getexplanation
	if (modes().verbosity > 2) {
		clog <<"Find T-theory explanation for " <<l <<"\n";
	}

	Propagator* solver = propagations[var(l)];
	assert(solver!=NULL); //If this happens, there is usually an error in the generated explanations!

	rClause explan = solver->getExplanation(l);
	assert(explan!=nullPtrClause);

	if (verbosity() >= 2) {
		clog <<"Implicit reason clause from the " <<solver->getName() <<" module ";
		MinisatID::print(l, sign(l) ? l_False : l_True);
		clog <<" : ";
		MinisatID::print(explan, *this);
		clog <<"\n";
	}

	return explan;*/

};

#endif /* EVENTQUEUE_HPP_ */
