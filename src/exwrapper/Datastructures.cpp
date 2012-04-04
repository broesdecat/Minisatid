#include "external/Datastructures.hpp"
#include "external/Remapper.hpp"

namespace MinisatID{
	template<>
	Convert<Lit>::LTo get(const Lit& lit, Remapper* remapper){
		return remapper->getLiteral(lit);
	}

	template<>
	Convert<Literal>::LTo get(const Literal& lit, Remapper* remapper){
		auto var = remapper->getVar(lit.getAtom());
		if(lit.hasSign()){
			return mkNegLit(var);
		}else{
			return mkPosLit(var);
		}
	}
}
