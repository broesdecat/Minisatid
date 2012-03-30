/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef PRINT_HPP_
#define PRINT_HPP_

#include <iostream>
#include "utils/Utils.hpp"
#include "utils/PrintMessage.hpp"

namespace MinisatID {

class PCSolver;

Lit getPrintableVar(Var v);

template<typename S>
std::string print(Var obj, S solver){
	return print(getPrintableVar(obj), solver);
}

std::string print(const Lit& obj, PCSolver const * const solver);
std::string print(const Lit& obj, lbool value, PCSolver const * const solver);
std::string print(const Lit& obj, const PCSolver& solver);
std::string print(const Lit& obj, lbool value, const PCSolver& solver);

template<class T>
T& operator<<(T& stream, const EqType& type){
	switch(type){
	case EqType::EQ:
		stream <<"=";
		break;
	case EqType::NEQ:
		stream <<"!=";
		break;
	case EqType::L:
		stream <<"<";
		break;
	case EqType::G:
		stream <<">";
		break;
	case EqType::GEQ:
		stream <<">=";
		break;
	case EqType::LEQ:
		stream <<"=<";
		break;
	}
	return stream;
}

template<class T>
T& operator<<(T& stream, AggType type){
	switch(type){
	case AggType::SUM:
		stream <<"sum";
		break;
	case AggType::CARD:
		stream <<"card";
		break;
	case AggType::MIN:
		stream <<"min";
		break;
	case AggType::MAX:
		stream <<"max";
		break;
	case AggType::PROD:
		stream <<"prod";
		break;
	}
	return stream;
}

}

#endif /* PRINT_HPP_ */
