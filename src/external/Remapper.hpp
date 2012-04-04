#ifndef REMAPPER_HPP_
#define REMAPPER_HPP_

#include <unordered_map>
#include "utils/Utils.hpp"
#include "utils/PrintMessage.hpp"

namespace MinisatID{

typedef std::unordered_map<int, int> atommap;

class Remapper{
protected:
	int maxnumber;
public:
	Remapper(): maxnumber(0){}
	Var		largestVar	() const { return maxnumber; }
private:
	//Maps from NON-INDEXED to INDEXED atoms
	atommap 		origtocontiguousatommapper, contiguoustoorigatommapper;

	void checkVar(const Atom& atom){
		if(atom<1 || atom == std::numeric_limits<int>::max()){
			throw idpexception(disAllowedVarNumbers());
		}
	}

public:
	Var getVar(const Atom& atom){
		checkVar(atom);

		auto i = origtocontiguousatommapper.find(atom);
		Var v = 0;
		if(i==origtocontiguousatommapper.cend()){
			origtocontiguousatommapper.insert(std::pair<int, int>(atom, maxnumber));
			contiguoustoorigatommapper.insert(std::pair<int, int>(maxnumber, atom));
			v = maxnumber++;
		}else{
			v = (*i).second;
		}
		return v;
	}

	Var getNewVar(){
		return maxnumber++;
	}

	bool wasInput(Var var) const{
		return contiguoustoorigatommapper.find(var)!=contiguoustoorigatommapper.cend();
	}

	Literal getLiteral(const Lit& lit) const{
		auto atom = contiguoustoorigatommapper.find(var(lit));
		MAssert(atom!=contiguoustoorigatommapper.cend());
		int origatom = (*atom).second;
		return mkLit(origatom, sign(lit));
	}
};

}

#endif /* REMAPPER_HPP_ */
