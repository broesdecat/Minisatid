#include "solvers/SATUtils.h"

#ifdef USEMINISAT
rClause nullPtrClause = NULL;

pClause getClauseRef(rClause rc){
	return *rc;
}

Lit mkLit(Var x, bool sign){
	return Lit(x, sign);
}
#endif

#ifdef USEMINISAT09Z
rClause nullPtrClause =  NULL;

pClause getClauseRef(rClause rc){
	return *rc;
}

Lit mkLit(Var x, bool sign){
	return Lit(x, sign);
}
#endif

#ifdef USEMINISAT22
rClause nullPtrClause = Minisat::CRef_Undef;

pClause getClauseRef(rClause rc){
	return rc;
}

#endif
