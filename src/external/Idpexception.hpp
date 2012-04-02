/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef IDPEXCEPTION_HPP_
#define IDPEXCEPTION_HPP_

#include <string>

namespace MinisatID {

// Generic exception
class idpexception: public std::exception{
private:
	std::string mess;

public:
	idpexception(const std::string& m): std::exception(), mess(m){		}
	idpexception(const char* m): std::exception(){
		mess.append(m);
	}

	~idpexception() throw(){}

	virtual const char* what() const throw(){
		return mess.c_str();
	}
};

idpexception notYetImplemented(const std::string& mess);

}


#endif /* IDPEXCEPTION_HPP_ */
