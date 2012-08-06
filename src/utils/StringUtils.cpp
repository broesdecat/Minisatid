/****************************************************************
 * Copyright 2010-2012 Katholieke Universiteit Leuven
 *  
 * Use of this software is governed by the GNU LGPLv3.0 license
 * 
 * Written by Broes De Cat, Stef De Pooter, Johan Wittocx
 * and Bart Bogaerts, K.U.Leuven, Departement Computerwetenschappen,
 * Celestijnenlaan 200A, B-3001 Leuven, Belgium
 ****************************************************************/

#include "StringUtils.hpp"

#include <string>
#include <sstream>
#include <locale>
#include <functional>
#include <algorithm>
#include <iostream>
#include <vector>

using namespace std;

bool startsWith(const string& s, const string& substring) {
	return s.substr(0, substring.size()) == substring;
}

// trim from start
string &ltrim(string &s) {
	s.erase(s.begin(), find_if(s.begin(), s.end(), not1(ptr_fun<int, int>(isspace))));
	return s;
}

// trim from end
string &rtrim(string &s) {
	s.erase(find_if(s.rbegin(), s.rend(), not1(ptr_fun<int, int>(isspace))).base(), s.end());
	return s;
}

// trim from both ends
string &trim(string &s) {
	return ltrim(rtrim(s));
}

string trim(const string& s) {
	auto temp = s;
	return ltrim(rtrim(temp));
}

string replaceAllIn(const string& text, const string& find, const string& replacement) {
	auto newtext = text;
	string::size_type position = newtext.find(find); // find first position
	while (position != string::npos) {
		newtext.replace(position, find.length(), replacement);
		position = newtext.find(find, position + 1);
	}
	return newtext;
}

string replaceAllAndTrimEachLine(const string& text, const string& find, const string& replacement) {
	std::stringstream input(text);
	stringstream trimmedlines;
	bool begin = true;
	while (true) {
		if (not begin) {
			trimmedlines << "\n";
		}
		begin = false;
		std::string line;
		std::getline(input, line);
		if (input.eof()) {
			trimmedlines << trim(line);
			break;
		}
		if (not input.good()) {
			break;
		}
		trimmedlines << trim(line);
	}
	return replaceAllIn(trimmedlines.str(), find, replacement);
}

template<class ContainerT>
void tokenize(const std::string& str, ContainerT& tokens, const std::string& delimiters = " ", const bool trimEmpty = false) {
	typedef typename ContainerT::value_type  vt;
	typedef typename ContainerT::value_type::size_type  st;
	std::string::size_type pos = 0, lastPos = 0;
	if(delimiters.size()==0){
		tokens.push_back(str);
		return;
	}
	while (true) {
		auto found = false;
		auto searchpos = lastPos;
		while(not found && pos!=std::string::npos){
			auto possiblepos = str.find_first_of(delimiters.front(), searchpos);
			if(possiblepos==std::string::npos || possiblepos+delimiters.size()>str.size()){
				pos=std::string::npos;
				break;
			}
			auto temppos = possiblepos;
			for(auto c:delimiters){
				if(str[temppos]!=c){
					searchpos = possiblepos + 1;
					break;
				}
				temppos++;
			}
			if(temppos==possiblepos+delimiters.size()){
				found = true;
				pos = possiblepos;
			}
		}

		if (pos == std::string::npos) {
			pos = str.length();

			if (pos != lastPos || not trimEmpty) {
				tokens.push_back(vt(str.data() + lastPos, (st) (pos - lastPos)));
			}

			break;
		} else {
			if (pos != lastPos || not trimEmpty) {
				tokens.push_back(vt(str.data() + lastPos, (st) (pos - lastPos)));
			}
		}

		lastPos = pos + delimiters.size();
	}
}

std::vector<std::string> split(const std::string &s, const std::string& delim) {
	std::vector<std::string> elems;
	tokenize(s, elems, delim);
	return elems;
}
