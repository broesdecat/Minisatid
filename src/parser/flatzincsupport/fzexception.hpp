/*
 * Copyright 2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef FZEXCEPTION_HPP_
#define FZEXCEPTION_HPP_

#include <exception>
#include <string>

class fzexception: public std::exception{
private:
	std::string mess;

public:
	fzexception(const std::string& mess): mess(mess){}
	~fzexception() throw(){}

	const char* what() const throw(){
		return mess.c_str();
	}
};

#endif /* FZEXCEPTION_HPP_ */
