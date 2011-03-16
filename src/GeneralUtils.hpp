/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef GENERALUTILS_HPP_
#define GENERALUTILS_HPP_

#include <vector>
#include <map>
#include <exception>
#include <string>
#include <assert.h>
#include <iostream>
#include <fstream>

#include "external/ExternalUtils.hpp"

#define report(...) ( fflush(stdout), fprintf(stderr, __VA_ARGS__), fflush(stderr) )

namespace MinisatID {
	//In elapsed seconds, making abstraction of other processes running on the system
	double cpuTime(void);

	// Support for deleting lists of pointer elements
	template<class T>
	void deleteList(std::vector<T*> l){
		for(class std::vector<T*>::const_iterator i=l.begin(); i!=l.end(); ++i){
			if(*i!=NULL){
				delete(*i);
			}
		}
		l.clear();
	}

	template<class T>
	void deleteList(std::vector<std::vector<T*> > l){
		for(class std::vector<std::vector<T*> >::const_iterator i=l.begin(); i!=l.end(); ++i){
			deleteList(*i);
		}
		l.clear();
	}

	template<class T, class K>
	void deleteList(std::map<K, T*> l){
		for(class std::map<K, T*>::const_iterator i=l.begin(); i!=l.end(); ++i){
			if((*i).second!=NULL){
				delete((*i).second);
			}
		}
		l.clear();
	}

	template<class T>
	bool fileIsReadable(T* filename) { //quick and dirty
		std::ifstream f(filename, std::ios::in);
		bool exists = f.is_open();
		if(exists){
			f.close();
		}
		return exists;
	}

}


#endif /* GENERALUTILS_HPP_ */
