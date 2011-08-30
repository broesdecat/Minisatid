/************************************
	LazyClauseSupport.cpp
	this file belongs to GidL 2.0
	(c) K.U.Leuven
************************************/

#include "external/LazyClauseSupport.hpp"

#include "modules/LazyGrounder.hpp"

using namespace MinisatID;

void LazyClauseRef::notifyCertainlyTrue(){
	getClause()->notifyCertainlyTrue();
}
void LazyClauseRef::notifyCertainlyFalse(){
	getClause()->notifyCertainlyFalse();
}
