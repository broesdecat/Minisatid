#include "solvers/SATUtils.h"

#ifdef USEMINISAT
Lit mkLit(Var x, bool sign){
	return Lit(x, sign);
}
#endif
#ifdef USEMINISAT09Z
Lit mkLit(Var x, bool sign){
	return Lit(x, sign);
}
#endif
