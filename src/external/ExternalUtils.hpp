/* * Copyright 2007-2011 Katholieke Universiteit Leuven * * Use of this software is governed by the GNU LGPLv3.0 license * * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium */
#ifndef EXTERNALUTILS_HPP_
#define EXTERNALUTILS_HPP_

#include <string>

#include <map>
#include <vector>
#include <string>
#include <cstdlib>

#include "GeneralUtils.hpp"

namespace MinisatID {

///////
// Generic atom and literal structures
///////

class Atom{
private:
	int atom; //Important: because of mutual exclusion of const members and a clean assignment operator, i did not make this constant, but semantically it should be

public:
	explicit Atom(int a): atom(a){ }
	int		getValue	() 				const { return atom; }

	bool operator==	(const Atom& a) const { return atom==a.atom; }
	bool operator<	(const Atom& a) const { return atom<a.atom; }
};

class Literal{
private:
	int lit;

public:
	//@pre: a is positive
	explicit Literal(int a, bool s = false): lit(s?-a:a){ assert(a>=0); }
	explicit Literal(Atom a, bool s = false): lit(s?-a.getValue():a.getValue()){ assert(a.getValue()>=0); }

	int		getValue()						const { return lit; }
	Atom 	getAtom() 						const { return Atom(lit<0?-lit:lit); }
	bool 	hasSign() 						const { return lit<0; }
	bool 	operator== (const Literal& l) 	const { return lit == l.lit; }
	bool 	operator< (const Literal& l) 	const {	return abs(lit) < abs(l.lit); }
	Literal operator~()						const { return Literal(getAtom(), lit>0?true:false); }
};

// A class representing a tuple of a literal and an associated weight
struct WLtuple{
	const Literal l;
	const Weight w;

	WLtuple(const Literal& l, const Weight& w): l(l), w(w){ }
	WLtuple operator=(const WLtuple& lw) const { return WLtuple(lw.l, lw.w); }
};typedef std::vector<Literal> literallist;typedef std::vector<std::vector<Literal> > modellist;enum ModelSaved { MODEL_NONE, MODEL_SAVED, MODEL_SAVING };

class Solution{
private:	const ModelExpandOptions options;
	int 		nbmodels;	literallist	temporarymodel;
	modellist	models; //IMPORTANT: for optimization problem, models will contain a series of increasingly better models	literallist assumptions;	bool		optimalmodelfound;	ModelSaved modelsave; //CRITICAL SECTION SUPPORT

public:
	Solution(ModelExpandOptions options):
			options(options),			nbmodels(0),			optimalmodelfound(false),			modelsave(MODEL_NONE){}
	~Solution(){};

	int 	getNbModelsFound	() const	{ return nbmodels; }
	int 	getNbModelsToFind	() const	{ return options.nbmodelstofind; }
	PrintModel 	getPrintOption	() const 	{ return options.printmodels; }
	SaveModel 	getSaveOption	() const 	{ return options.savemodels; }
	Inference 	getInferenceOption	() const 	{ return options.search; }	const ModelExpandOptions& getOptions() const { return options; }	const modellist& 	getModels() { return models; } //IMPORTANT: no use calling it when models are not being saved.	const literallist& getAssumptions	() { return assumptions; }

	void 	addModel(literallist model, bool currentlybest) {		if(modelsave==MODEL_NONE || (modelsave==MODEL_SAVED && getSaveOption()==SAVE_ALL)){			nbmodels++;		}else if(modelsave==MODEL_SAVING){ //Error in saving previous model, so abort			throw idpexception("Previous model failed to save, cannot guarantee correctness.\n");		}
		if(getSaveOption()==SAVE_BEST){			if(modelsave!=MODEL_NONE){				temporarymodel = models.back();			}		}		modelsave = MODEL_SAVING;		models.push_back(model);		modelsave = MODEL_SAVED;
	}	const literallist& getBestModelFound() const{		assert(modelsave!=MODEL_NONE);		if(modelsave==MODEL_SAVED){			return models.back();		}else{			return temporarymodel;		}	}	bool	hasOptimalModel			() const	{ return optimalmodelfound; }	void	notifyOptimalModelFound	()			{ optimalmodelfound = true;	}
};

}

#endif /*EXTERNALUTILS_HPP_*/
