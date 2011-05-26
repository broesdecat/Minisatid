/*
 * PCLogger.hpp
 *
 *  Created on: May 26, 2011
 *      Author: broes
 */

#ifndef PCLOGGER_HPP_
#define PCLOGGER_HPP_

class PCLogger{
private:
	std::vector<int> occurrences;
	int propagations;

public:
	PCLogger();

	void addPropagation() { ++propagations; }
	int getNbPropagations() const { return propagations; }
	void addCount(Var v);
	int getCount(Var v) const;

};

#endif /* PCLOGGER_HPP_ */
