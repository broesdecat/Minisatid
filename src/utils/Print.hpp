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

/**
 * Verbosity rules:
 * level 0: no output
 * level 1: statistics information
 * level 2: initialization information + ?
 * TODO
 */

namespace MinisatID {

class WrapperPimpl;

void setTranslator(WrapperPimpl* translator);

template<typename T>
Lit getPrintableVar(T v) { return mkPosLit(v); }

template<class T>
std::string print(const T& obj);

template<class T>
T& operator<<(T& stream, const Lit& lit){
	stream << print(lit);
	return stream;
}

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

template<class T>
void print(const T& lit, const lbool val);

template<class S>
void print(S * const s);

template<class S>
void print(rClause c, const S& s);

template<typename List>
void printList(const List& list, const std::string& between){
	bool begin = true;
	for(auto j=list.cbegin(); j<list.cend(); j++){
		if(not begin){
			std::clog <<between;
		}
		begin = false;
		std::clog <<*j;
	}
}

}

#endif /* PRINT_HPP_ */
