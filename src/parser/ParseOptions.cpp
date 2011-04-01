/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#include "parser/ParseOptions.hpp"
#include "GeneralUtils.hpp"

#include <vector>
#include <string>
#include <iostream>

#include <tclap/CmdLine.h>
#include "external/ResourceManager.hpp"

#include "utils/Print.hpp"

using namespace std;
using namespace MinisatID;
using namespace MinisatID::Print;

SolverOption modes; //Used by parser, initialized before parsing!

struct Opt{
	virtual ~Opt(){}
	virtual void parse() = 0;
};

template <typename T>
struct NoValsOption: public Opt{
	const string shortopt;
	const string longopt;
	const string mess;
	const T defaultval;
	TCLAP::ValueArg<T>* arg;
	T& modesarg;

	NoValsOption(const string &s, const string &l, const string& type, T& modesarg, TCLAP::CmdLine& cmd, const string &m):
		shortopt(s), longopt(l), mess(m), defaultval(modesarg), modesarg(modesarg){

		arg = new TCLAP::ValueArg<T>(shortopt,longopt, mess, false, defaultval, type, cmd);
	};

	~NoValsOption(){
		delete arg;
	}

	void parse(){
		modesarg = arg->getValue();
	}
};

template <typename T, typename T2>
struct Option: public Opt{
	const string shortopt;
	const string longopt;
	const string mess;
	const T defaultval;
	const vector<T> vals;
	const vector<pair<T2, string> > desc; //<tclapvalue, valuedescription>
	TCLAP::ValuesConstraint<T2>* formatsconstr;
	TCLAP::ValueArg<T2>* arg;
	T& modesarg;

	Option(const string &s, const string &l, const vector<T>& vals, const vector<pair<T2, string> >& desc, T& modesarg, TCLAP::CmdLine& cmd, const string &m):
		shortopt(s), longopt(l), mess(m), defaultval(modesarg), vals(vals), desc(desc), modesarg(modesarg){
		vector<T2> constrvals;
		for(typename vector<pair<T2, string> >::const_iterator i=desc.begin(); i<desc.end(); ++i){
			constrvals.push_back((*i).first);
		}
		formatsconstr = new TCLAP::ValuesConstraint<T2>(constrvals);

		stringstream ss;

		assert(desc.size()>0 && vals.size()==desc.size());
		T2 tclapdefault = desc[0].first;
		bool found = false;
		ss <<mess <<":" <<endl;
		for(typename vector<T>::size_type i=0; i<vals.size(); ++i){
			ss <<"\t<" <<desc[i].first <<"|" <<desc[i].second <<">";
			if(vals[i]==defaultval){
				tclapdefault = desc[i].first;
				ss <<"*";
				found = true;
			}
			ss <<endl;
		}
		assert(found);

		arg = new TCLAP::ValueArg<T2>(shortopt,longopt, ss.str(), false, tclapdefault, formatsconstr, cmd);
	};

	~Option(){
		delete formatsconstr;
		delete arg;
	}

	void parse(){
		//cerr <<longopt <<" " <<arg->getValue() <<endl;
		bool found = false;
		uint i=0;
		for(; i<desc.size(); ++i){
			if(desc[i].first==arg->getValue()){
				found = true;
				break;
			}
		}
		assert(found);
		modesarg = vals[i];
	}
};

//Return false if parsing failed
bool MinisatID::parseOptions(int argc, char** argv){
	string outputfile = "";

	vector<Opt*> options;

	vector<bool> yesnovals; //Maintain this order in desc vectors!
	yesnovals.push_back(true);
	yesnovals.push_back(false);

	vector<INPUTFORMAT> formatvals;
	vector<pair<string, string> > formatdesc;
	formatvals.push_back(FORMAT_FODOT); formatdesc.push_back(pair<string, string>("fodot", "propositional FO(.)"));
	formatvals.push_back(FORMAT_ASP); formatdesc.push_back(pair<string, string>("asp", "propositional LParse ASP"));
	formatvals.push_back(FORMAT_OPB); formatdesc.push_back(pair<string, string>("opb", "open pseudo-boolean"));

	vector<OUTPUTFORMAT> transvals;
	vector<pair<string, string> > transdesc;
	transvals.push_back(TRANS_FODOT); transdesc.push_back(pair<string, string>("fodot", "Translate model into FO(.) structure"));
	transvals.push_back(TRANS_ASP); transdesc.push_back(pair<string, string>("asp", "Translate model into ASP facts"));
	transvals.push_back(TRANS_PLAIN); transdesc.push_back(pair<string, string>("plain", "Return model in integer format"));

	vector<pair<string, string> > checkcyclesdesc;
	checkcyclesdesc.push_back(pair<string, string>("yes", "Check"));
	checkcyclesdesc.push_back(pair<string, string>("no", "Don't check"));
	vector<pair<string, string> > ecnfgraphdesc;
	ecnfgraphdesc.push_back(pair<string, string>("yes", "Generate"));
	ecnfgraphdesc.push_back(pair<string, string>("no", "Don't generate"));
	vector<pair<string, string> > remapdesc;
	remapdesc.push_back(pair<string, string>("yes", "Remap"));
	remapdesc.push_back(pair<string, string>("no", "Don't remap"));

	vector<pair<string, string> > bumpaggonnotifydesc;
	bumpaggonnotifydesc.push_back(pair<string, string>("yes", "Bump"));
	bumpaggonnotifydesc.push_back(pair<string, string>("no", "Don't bump"));

	vector<pair<string, string> > bumpidonstartdesc;
	bumpidonstartdesc.push_back(pair<string, string>("yes", "Bump"));
	bumpidonstartdesc.push_back(pair<string, string>("no", "Don't bump"));

	vector<pair<string, string> > subsetminimdesc;
	subsetminimdesc.push_back(pair<string, string>("yes", "Minimize"));
	subsetminimdesc.push_back(pair<string, string>("no", "Don't minimize"));

	vector<pair<string, string> > asapaggpropdesc;
	asapaggpropdesc.push_back(pair<string, string>("yes", "Early"));
	asapaggpropdesc.push_back(pair<string, string>("no", "Late"));

	vector<pair<string, string> > pbsolverdesc;
	pbsolverdesc.push_back(pair<string, string>("yes", "Use pbsolver"));
	pbsolverdesc.push_back(pair<string, string>("no", "Don't use pbsolver"));

	vector<pair<string, string> > watcheddesc;
	watcheddesc.push_back(pair<string, string>("yes", "Use smart watches"));
	watcheddesc.push_back(pair<string, string>("no", "Use full watches"));

	vector<pair<string, string> > aggheurdesc;
	aggheurdesc.push_back(pair<string, string>("yes", "Use aggregate heuristic"));
	aggheurdesc.push_back(pair<string, string>("no", "Don't use aggregate heuristic"));

	vector<POLARITY> polvals;
	vector<pair<string, string> > poldesc;
	polvals.push_back(POL_TRUE); poldesc.push_back(pair<string, string>("true", "true-first"));
	polvals.push_back(POL_FALSE); poldesc.push_back(pair<string, string>("false", "false-first"));
	polvals.push_back(POL_RAND); poldesc.push_back(pair<string, string>("rand", "random"));
	polvals.push_back(POL_STORED); poldesc.push_back(pair<string, string>("stored", "history-based"));

	vector<int> aggsavingvals;
	vector<pair<int, string> > aggsavingdesc;
	aggsavingvals.push_back(0); aggsavingdesc.push_back(pair<int, string>(0, "add clause on propagation"));
	aggsavingvals.push_back(1); aggsavingdesc.push_back(pair<int, string>(1, "save clause on propagation"));
	aggsavingvals.push_back(2); aggsavingdesc.push_back(pair<int, string>(2, "save reason on propagation"));

	vector<DEFFINDCS> defsearchvals;
	vector<pair<string, string> > defsearchdesc;
	defsearchvals.push_back(always); defsearchdesc.push_back(pair<string, string>("always", "After each series of propagations"));
	defsearchvals.push_back(adaptive); defsearchdesc.push_back(pair<string, string>("adapt", "Adaptive heuristic"));
	defsearchvals.push_back(lazy); defsearchdesc.push_back(pair<string, string>("lazy", "When a model has been found for the completion"));

	vector<DEFSEM> defsemvals;
	vector<pair<string, string> > defsemdesc;
	defsemvals.push_back(DEF_WELLF); defsemdesc.push_back(pair<string, string>("wellf", "Well-founded semantics"));
	defsemvals.push_back(DEF_STABLE); defsemdesc.push_back(pair<string, string>("stable", "Stable semantics"));
	defsemvals.push_back(DEF_COMP); defsemdesc.push_back(pair<string, string>("comp", "Completion semantics"));

	vector<int> idsavingvals;
	vector<pair<int, string> > idsavingdesc;
	idsavingvals.push_back(0); idsavingdesc.push_back(pair<int, string>(0, "add clause on propagation"));
	idsavingvals.push_back(1); idsavingdesc.push_back(pair<int, string>(1, "save clause on propagation"));

	TCLAP::CmdLine cmd = TCLAP::CmdLine(getProgramInfo(), '=', getProgramVersion()); //second arg is delimiter: -option<delim>value

	TCLAP::UnlabeledValueArg<string> inputfilearg("inputfile", "The file which contains the input theory. If not provided, the standard-in stream is assumed as input.", false, "", "inputfile", cmd);

	options.push_back(new NoValsOption<int>		("n","nbmodels", 	"int",
			modes.nbmodels, cmd, "The number of models to search for."));
	options.push_back(new NoValsOption<int>		("","verbosity", 	"int",
			modes.verbosity, cmd, "The level of output to generate."));
	options.push_back(new NoValsOption<int>		("","randomseed", 	"int",
			modes.randomseed, cmd, "The random seed the solver should use."));
	options.push_back(new NoValsOption<long>	("","ufsvarintro", 	"long",
			modes.ufsvarintrothreshold, cmd,"Threshold (compared with ufssize*loopfsize) above which an extra variable is introduced when an unfounded set is found."));
	options.push_back(new NoValsOption<double>	("","rnd-freq", 	"double",
			modes.rand_var_freq, cmd,"The frequency with which to make a random choice (between 0 and 1)."));
	options.push_back(new NoValsOption<double>	("","decay", 		"double",
			modes.var_decay, cmd, "The decay of variable activities within the SAT-solver (larger than or equal to 0)."));
	options.push_back(new NoValsOption<string>	("o","outputfile", 	"file",
			outputfile, cmd,"The outputfile to use to write out models."));
    options.push_back(new NoValsOption<string>	("","primesfile",	"file",
			 modes.primesfile, cmd,"File containing a list of prime numbers to use for finding optimal bases. Has to be provided if using pbsolver."));
	options.push_back(new Option<INPUTFORMAT, string>("f", "format", formatvals, formatdesc,
			modes.format, cmd, "The format of the input theory"));
	options.push_back(new Option<OUTPUTFORMAT, string>("", "outputformat", transvals, transdesc,
			modes.transformat, cmd, "The requested output format (only relevant if translation information is provided)."));
	options.push_back(new Option<bool, string>	("", "ecnfgraph", 	yesnovals, ecnfgraphdesc,
			modes.printcnfgraph, cmd, "Choose whether to generate a .dot graph representation of the ecnf"));
	options.push_back(new Option<bool, string>	("", "cyclefreeness-check", yesnovals, checkcyclesdesc,
			modes.checkcyclefreeness, cmd, "Check the correctness of the inductive definition algorithm."));
	options.push_back(new Option<bool, string>	("r", "remap", 		yesnovals, remapdesc,
			modes.remap, cmd, "Choose whether to remap literals from the input structure to a contiguous internal representation"));
	options.push_back(new Option<bool, string>	("","bumpagg", 		yesnovals, bumpaggonnotifydesc,
			modes.bumpaggonnotify, cmd,"Choose whether to bump variable activity on aggregate propagation"));
	options.push_back(new Option<bool, string>	("","bumpid", 		yesnovals, bumpidonstartdesc,
			modes.bumpidonstart, cmd, "Choose whether to bump variable activity on ID initialization"));
	options.push_back(new Option<bool, string>	("","minimexplan", 	yesnovals, subsetminimdesc,
			modes.subsetminimizeexplanation, cmd, "Choose whether to minimize aggregate explanations"));
	options.push_back(new Option<bool, string>	("","asapaggprop", 	yesnovals, asapaggpropdesc,
			modes.asapaggprop, cmd, "Choose whether to propagate aggregates as fast as possible"));
	options.push_back(new Option<bool, string>	("","pbsolver", 	yesnovals, pbsolverdesc,
			modes.pbsolver, cmd,"Choose whether to translate pseudo-boolean constraints to SAT"));
	options.push_back(new NoValsOption<double>	("","watch-ratio", 	"double",
			modes.watchesratio, cmd,"The ratio of watches to set literals under which the watched algorithm is used."));
	options.push_back(new Option<bool,string>	("","use-agg-heur", 	yesnovals, aggheurdesc,
			modes.useaggheur, cmd,"Use a specialized aggregate heuristic."));
	options.push_back(new Option<POLARITY, string>("","polarity", 	polvals, poldesc,
			modes.polarity, cmd, "The default truth value choice of variables"));
	options.push_back(new Option<int, int>("","aggsaving", 			aggsavingvals, aggsavingdesc,
			modes.aggclausesaving, cmd, "How to handle propagation reasons for aggregates"));
	options.push_back(new Option<DEFFINDCS, string>("","defsearch", defsearchvals, defsearchdesc,
			modes.defn_strategy, cmd,"Choose the unfounded-set search-frequency"));
	options.push_back(new Option<DEFSEM, string>("","defsem", 		defsemvals, defsemdesc,
			modes.defsem, cmd,"Choose the semantics of the inductive definitions"));
	options.push_back(new Option<int, int>("","idsaving", 			idsavingvals, idsavingdesc,
			modes.idclausesaving, cmd, "Choose how to handle propagation reasons for inductive definitions"));

	try {
		cmd.parse(argc, argv);
	} catch (TCLAP::ArgException &e){
		std::cerr << "Error: " << e.error() << " for arg " << e.argId() << std::endl;
		return false;
	}

	for(vector<Opt*>::const_iterator i=options.begin(); i<options.end(); ++i){
		(*i)->parse();
	}

	if(inputfilearg.isSet()){
		setInputFileUrl(inputfilearg.getValue());
	}
	if(outputfile.compare("")!=0){
		setOutputFileUrl(outputfile);
	}

	deleteList<Opt>(options);

	if(!modes.verifyOptions()){
		return false;
	}

	return true;
}
