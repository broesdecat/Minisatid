/****************************************************************
 * Copyright 2010-2012 Katholieke Universiteit Leuven
 *  
 * Use of this software is governed by the GNU LGPLv3.0 license
 * 
 * Written by Broes De Cat, Stef De Pooter, Johan Wittocx
 * and Bart Bogaerts, K.U.Leuven, Departement Computerwetenschappen,
 * Celestijnenlaan 200A, B-3001 Leuven, Belgium
****************************************************************/

#ifndef IDP_STRINGTRIM_HPP_
#define IDP_STRINGTRIM_HPP_

#include <string>
#include <vector>

bool startsWith(const std::string& string, const std::string& substring);

// trim from start
std::string &ltrim(std::string &s);

// trim from end
std::string &rtrim(std::string &s);

// trim from both ends
std::string &trim(std::string &s);

std::string trim(const std::string& s);

std::string replaceAllIn(const std::string& text, const std::string& find, const std::string& replacement);

std::string replaceAllAndTrimEachLine(const std::string& text, const std::string& find, const std::string& replacement);

std::vector<std::string> split(const std::string &s, const std::string& delim);

#endif /* IDP_STRINGTRIM_HPP_ */
