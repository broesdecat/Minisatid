/****************************************************************
 * Copyright 2010-2012 Katholieke Universiteit Leuven
 *  
 * Use of this software is governed by the GNU LGPLv3.0 license
 * 
 * Written by Broes De Cat, Stef De Pooter, Johan Wittocx
 * and Bart Bogaerts, K.U.Leuven, Departement Computerwetenschappen,
 * Celestijnenlaan 200A, B-3001 Leuven, Belgium
****************************************************************/

#ifndef IDP_NUMERICLIMITS_HPP_
#define IDP_NUMERICLIMITS_HPP_

/**
 * Prevent bug with numeric_limits<double>::min() which is the smallest POSITIVE double value.
 * Prevent more eclipse warnings
 */

#include <limits>

template<typename T>
T getMinElem() {
	return std::numeric_limits<T>::min();
}

template<>
double getMinElem();

template<typename T>
T getMaxElem() {
	return std::numeric_limits<T>::max();
}

#endif /* IDP_NUMERICLIMITS_HPP_ */
