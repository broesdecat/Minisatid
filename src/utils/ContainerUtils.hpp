/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef MINISATID_CONTAINERUTILS_HPP_
#define MINISATID_CONTAINERUTILS_HPP_

#include <cstdlib>
#include <map>
#include <string>
#include <vector>

namespace MinisatID {

// Support for deleting lists of pointers
template<class T>
void deleteList(std::vector<T*>& l) {
	for (auto i = l.cbegin(); i != l.cend(); ++i) {
		if (*i != NULL) {
			delete (*i);
		}
	}
	l.clear();
}

template<class T>
void deleteList(std::vector<std::vector<T*> >& l) {
	for (auto i = l.begin(); i != l.end(); ++i) {
		deleteList(*i);
	}
	l.clear();
}

template<class T, class K>
void deleteList(std::map<K, T*>& l) {
	for (auto i = l.cbegin(); i != l.cend(); ++i) {
		if ((*i).second != NULL) {
			delete ((*i).second);
		}
	}
	l.clear();
}

template<class T, class K>
void deleteList(std::map<K, std::map<K, std::vector<T*> > >& l) {
	for (auto i = l.cbegin(); i != l.cend(); ++i) {
		for (auto j = (*i).second.cbegin(); j != (*i).second.cend(); ++j) {
			for (auto k = (*j).second.cbegin(); k != (*j).second.cend(); ++k) {
				if ((*k).second != NULL) {
					delete ((*k).second);
				}
			}
		}
	}
	l.clear();
}

template<class List, class Elem>
bool contains(const List& l, const Elem& e) {
	return l.find(e) != l.cend();
}

template<typename List, typename Stream>
void printConcatBy(const List& list, const std::string& concat, Stream& stream){
	bool begin = true;
	for(auto i=list.cbegin(); i<list.cend(); ++i) {
		if(not begin){
			stream <<concat;
		}
		begin = false;
		stream <<*i;
	}
}

}

#endif //MINISATID_CONTAINERUTILS_HPP_
