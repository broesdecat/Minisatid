/*
 * ParseOptions.hpp
 *
 *  Created on: Nov 29, 2010
 *      Author: broes
 */

#ifndef PARSEOPTIONS_HPP_
#define PARSEOPTIONS_HPP_


namespace MinisatID{
	bool parseOptions(int argc, char** argv);

	enum INPUTFORMAT {FORMAT_FODOT, FORMAT_ASP, FORMAT_OPB};
	INPUTFORMAT getChosenFormat();
}

#endif /* PARSEOPTIONS_HPP_ */
