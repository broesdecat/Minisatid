/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Marien, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef MINISATID_OPTIONS_HPP_
#define MINISATID_OPTIONS_HPP_

#include <string>
#include <ostream>

namespace MinisatID {

// Definitional options
enum DEFFINDCS {
	always, adaptive, lazy
};
// Unfounded set search frequency
enum DEFMARKDEPTH {
	include_cs
};
// Originally also contained stop_at_cs, which is no longer correct
// when a guaranteed cycle-free justification is used!

// Unfounded set search strategy
enum DEFSEARCHSTRAT {
	breadth_first /*, depth_first*/
};

// Definitional semantics
enum DEFSEM {
	DEF_STABLE, DEF_WELLF, DEF_COMP
};

enum class SATVAL {
	UNSAT, POS_SAT
};
void operator&=(SATVAL& orig, SATVAL add);

enum class Polarity {
	TRUE, FALSE, STORED, RAND
};
// SAT-solver polarity option

enum class InputFormat {
	FODOT, ASP, OPB, FLATZINC
};
enum class OutputFormat {
	FODOT, ASP, PLAIN, FZ, OPB, DEFAULT
};
enum class Inference {
	PROPAGATE, MODELEXPAND, PRINTTHEORY, PRINTGRAPH
};
enum class Heuristic {
	CLASSIC, VMTF, DIRECTRELEVANCE, STRONGRELEVANCE
};

// General options for all inferences
class SolverOption {
public:
	Inference inference;
	InputFormat format;
	OutputFormat transformat;
	int verbosity;
	bool solvingstats;
	int randomseed;
	int nbmodels;
	DEFSEM defsem;
	DEFSEARCHSTRAT ufs_strategy;
	DEFFINDCS defn_strategy;
	DEFMARKDEPTH defn_search;
	bool checkcyclefreeness;
	int idclausesaving, aggclausesaving;
	bool selectOneFromUFS;
	bool tocnf; // FIXME pbsolver is incorrect, do not enable this!!!
	bool splitagg;
	double watchesratio;
	std::string primesfile;
	double rand_var_freq, var_decay;
	Polarity polarity;
	bool bumpaggonnotify, bumpidonstart;
	long ufsvarintrothreshold;
	bool subsetminimizeexplanation, currentlevelfirstinexplanation, innogoodfirstinexplanation;
	bool lazy; // If false, guarantees the solver that no constraints will be lazily added afterwards (not internal stuff such as decomposition or lazy learning)
	bool lazyheur, watchedrelevance;
	bool expandimmediately; // Debug option to test lazy grounding overhead by expanding everything asap
	bool usegecode;
	std::string outputfile;
	int maxNbOfLearnedClauses;
	bool fullmodelcheck; // Check whether the model satisfies all constraints
	bool usesimplifier; // Use code that caches all constraints, applies some simplifications (removing duplicate variables, ...) and then goes on to propagation and solving.
	bool userandomizedrestarts;
	bool flatzinc_a;
	Heuristic heuristic;

	SolverOption();

	bool verifyOptions() const;
	std::string getPrimesFile() const;
	void print(std::ostream& stream) const;
};

enum class Models {
	ALL, BEST, NONE
};

class ModelExpandOptions {
public:
	Models printmodels;
	Models savemodels;
	int nbmodelstofind;

	ModelExpandOptions(int nbmodelstofind, Models printmodels, Models savemodels)
			: printmodels(printmodels), savemodels(savemodels), nbmodelstofind(nbmodelstofind) {
	}
};

}

#endif /* MINISATID_OPTIONS_HPP_ */
