/*
 * CPScript.hpp
 *
 *  Created on: Jul 12, 2010
 *      Author: broes
 */

#ifndef CPSCRIPT_HPP_
#define CPSCRIPT_HPP_

#include "solvers/cpsolver/CPUtils.hpp"

namespace CP{

	using namespace Gecode;

	typedef vector<BoolVar> vboolv;
	typedef vector<IntVar> vintv;
	typedef vboolv::size_type boolvarindex;
	typedef vintv::size_type intvarindex;

	class CPScript: public Space{
	private:
		vboolv boolvars;
		vintv intvars;

	public:
		CPScript();
		CPScript(bool share, CPScript& s);
		virtual CPScript* copy(bool share);

		const vintv& 	getIntVars()	const { return intvars; }
		const vboolv& 	getBoolVars()	const { return boolvars; }

		// Return the mapping of the Var to an integer number
		intvarindex		addIntVar(int min, int max);
		boolvarindex	addBoolVar();

		void 			addBranchers();
	};

	ostream& operator <<(ostream& ostream, const CPScript& script);
}

#endif /* CPSCRIPT_HPP_ */
