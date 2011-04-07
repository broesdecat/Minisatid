/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef CPSCRIPT_HPP_
#define CPSCRIPT_HPP_

#include "modules/cpsolver/CPUtils.hpp"

namespace MinisatID{
	typedef std::vector<Gecode::BoolVar> vboolv;
	typedef std::vector<Gecode::IntVar> vintv;
	typedef vboolv::size_type boolvarindex;
	typedef vintv::size_type intvarindex;

	class CPScript: public Gecode::Space{
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
		intvarindex 	addIntVar(const std::vector<int>& values);
		boolvarindex	addBoolVar();

		void 			addBranchers();
	};

	std::ostream& operator <<(std::ostream& stream, const CPScript& script);
}

#endif /* CPSCRIPT_HPP_ */
