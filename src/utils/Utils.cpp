//LICENSEPLACEHOLDER
#include "utils/Utils.hpp"
#include <string>

using namespace std;
using namespace MinisatID;

bool MinisatID::isPositive(Lit l) {
	return !sign(l);
}
Lit MinisatID::createNegativeLiteral(Var i) {
	return mkLit(i, true);
}
Lit MinisatID::createPositiveLiteral(Var i) {
	return mkLit(i, false);
}

bool MinisatID::compareWLByLits(const WL& one, const WL& two) {
	return var(one.getLit()) < var(two.getLit());
}

bool MinisatID::compareWLByWeights(const WL& one, const WL& two) {
	return one.getWeight() < two.getWeight();
}
