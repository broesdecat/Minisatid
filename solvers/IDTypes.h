/*
 * idsolvertypes.h
 *
 *  Created on: Mar 20, 2010
 *      Author: broes
 */

#ifndef IDSOLVERTYPES_H_
#define IDSOLVERTYPES_H_

enum FINDCS		{ always, adaptive, lazy};
enum MARKDEPTH	{ include_cs, stop_at_cs};
enum SEARCHSTRAT{ breadth_first, depth_first};
enum IDSEM		{STABLE,WELLF};

/**
 * The different possible types of definitions.
 * If a variable is NONDEFALL, no definition is associated with it.
 * If a variable is NONDEFPOS, a definition is associated with it, but there is no recursion through it in the POSITIVE dependency graph
 * 		but there might be recursion over negation (relevant for the well-founded model)
 */
enum DefType	{NONDEFTYPE, DISJ, CONJ, AGGR};
enum DefOcc		{NONDEFOCC, POSLOOP, MIXEDLOOP, BOTHLOOP};
enum UFS 		{NOTUNFOUNDED, UFSFOUND, STILLPOSSIBLE, OLDCHECK};

#endif /* IDSOLVERTYPES_H_ */
