#ifndef UTILS_H_
#define UTILS_H_

#include <vector>

using namespace std;

template<class T>
void deleteList(vector<T*> l){
	for(class vector<T*>::iterator i=l.begin(); i<l.end(); i++){
		if(*i!=NULL){
			delete(*i);
		}
	}
	l.clear();
}

#endif /* UTILS_H_ */
