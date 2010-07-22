/*
 * solverfwd.h
 *
 *  Created on: Mar 20, 2010
 *      Author: broes
 */

#ifndef SOLVERFWD_H_
#define SOLVERFWD_H_

#include <tr1/memory>
#include <stdlib.h>

using namespace std;
using namespace tr1;

#include "solver3/SolverTypes.hpp"
#include "ExternalUtils.hpp"

class idpexception: public std::exception{
//private:
//	const char* mess;
public:
	idpexception(): std::exception(){
	}

	virtual const char* what() const throw(){
		return "";
	}
};

#endif /* SOLVERFWD_H_ */
