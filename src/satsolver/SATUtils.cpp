/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#include "satsolver/SATUtils.hpp"

using namespace MinisatID;

#ifdef USEMINISAT
rClause MinisatID::nullPtrClause = NULL;

pClause MinisatID::getClauseRef(rClause rc){
	return *rc;
}

Lit MinisatID::mkLit(Var x, bool sign){
	return Lit(x, sign);
}

double MinisatID::getDefaultDecay(){
	return 1/0.95;
}
double MinisatID::getDefaultRandfreq(){
	return 0.02;
}
POLARITY MinisatID::getDefaultPolarity(){
	return POL_STORED;
}
#endif

#ifdef USEMINISAT09Z
rClause MinisatID::nullPtrClause =  NULL;

pClause MinisatID::getClauseRef(rClause rc){
	return *rc;
}

Lit MinisatID::mkLit(Var x, bool sign){
	return Lit(x, sign);
}

double MinisatID::getDefaultDecay(){
	return 1/0.95;
}
double MinisatID::getDefaultRandfreq(){
	return 0.02;
}
POLARITY MinisatID::getDefaultPolarity(){
	return POL_STORED;
}
#endif

#ifdef USEMINISAT22
rClause MinisatID::nullPtrClause = Minisat::CRef_Undef;

pClause MinisatID::getClauseRef(rClause rc){
	return rc;
}

double MinisatID::getDefaultDecay(){
	return 0.95;
}
double MinisatID::getDefaultRandfreq(){
	return 0;
}
POLARITY MinisatID::getDefaultPolarity(){
	return POL_STORED;
}
#endif
