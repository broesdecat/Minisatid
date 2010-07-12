/*
 * CPScript.hpp
 *
 *  Created on: Jul 12, 2010
 *      Author: broes
 */

#ifndef CPSCRIPT_HPP_
#define CPSCRIPT_HPP_

#include <vector>

#include <gecode/kernel.hh>
#include <gecode/driver.hh>
#include <gecode/int.hh>
#include <gecode/minimodel.hh>

namespace CP{

	using namespace Gecode;
	using namespace std;

	class CPScript: public Space{
	private:
		vector<BoolVar> boolvars;
		vector<IntVar> intvars;

	public:
		CPScript();
		CPScript(bool share, CPScript& s);
		virtual CPScript* copy(bool share);

		const vector<IntVar>& getIntVars() const { return intvars; }
		const vector<BoolVar>& getBoolVars() const { return boolvars; }

		bool isTrue(int var) const{
			return boolvars[var].assigned() && boolvars[var].in(1);
		}

		bool isFalse(int var) const {
			return boolvars[var].assigned() && boolvars[var].in(0);
		}

		bool isAssigned(int var) const{
			return boolvars[var].assigned();
		}

		vector<IntVar>::size_type addIntVar(int min, int max){
			intvars.push_back(IntVar(*this, min, max));
			return intvars.size()-1;
		}
		vector<BoolVar>::size_type addBoolVar(){
			boolvars.push_back(BoolVar(*this, 0, 1));
			return boolvars.size()-1;
		}
	};

	ostream& operator <<(ostream& ostream, const CPScript& script);
}

#endif /* CPSCRIPT_HPP_ */
