/************************************
	LazyClauseSupport.cpp
	this file belongs to GidL 2.0
	(c) K.U.Leuven
************************************/

#include "external/LazyClauseSupport.hpp"

#include "modules/LazyClause.hpp"

using namespace MinisatID;

void LazyClauseRef::notifyFullyGrounded(){
	clause->notifyFullyGround();
}
void LazyClauseRef::notifyCertainlyTrue(){
	clause->notifyCertainlyTrue();
}
void LazyClauseRef::notifyCertainlyFalse(){
	clause->notifyCertainlyFalse();
}
