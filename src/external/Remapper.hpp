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
		if(atom.getValue()<1 || atom.getValue() == std::numeric_limits<int>::max()){
			throw idpexception(disAllowedVarNumbers());
		}
	}

public:
	Var getVar(const Atom& atom){
		checkVar(atom);

		auto i = origtocontiguousatommapper.find(atom.getValue());
		Var v = 0;
		if(i==origtocontiguousatommapper.cend()){
			origtocontiguousatommapper.insert(std::pair<int, int>(atom.getValue(), maxnumber));
			contiguoustoorigatommapper.insert(std::pair<int, int>(maxnumber, atom.getValue()));
			v = maxnumber++;
		}else{
			v = (*i).second;
		}
		return v;
	}

	Var getNewVar(){
		return maxnumber++; // FIXME check invariants on the data structures!
	}

	bool wasInput(Var var) const{
		return contiguoustoorigatommapper.find(var)!=contiguoustoorigatommapper.cend();
	}

	Literal getLiteral(const Lit& lit) const{
		auto atom = contiguoustoorigatommapper.find(var(lit));
		MAssert(atom!=contiguoustoorigatommapper.cend());
		int origatom = (*atom).second;
		return Literal(origatom, sign(lit));
	}

	bool hasVar(const Atom& atom, Var& mappedvarifexists) const{
		auto i = origtocontiguousatommapper.find(atom.getValue());
		if(i==origtocontiguousatommapper.cend()){
			return false;
		}else{
			mappedvarifexists = (*i).second;
			return true;
		}
	}
};

template<typename Remapper>
bool canBackMapLiteral(const Lit& lit, const Remapper& r) {
	return r.wasInput(var(lit));
}

template<typename Remapper>
Literal getBackMappedLiteral(const Lit& lit, const Remapper& r) {
	assert(canBackMapLiteral(lit, r));
	return r.getLiteral(lit);
}

}

#endif /* REMAPPER_HPP_ */
