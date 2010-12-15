/*
 * ParseOptions.cpp
 *
 *  Created on: Nov 29, 2010
 *      Author: broes
 */

#include "parser/ParseOptions.hpp"

#include <vector>
#include <string>
#include <iostream>

#include <tclap/CmdLine.h>
#include "satsolver/SATUtils.hpp"
#include "external/ExternalUtils.hpp"
#include "parser/ResourceManager.hpp"
#include "utils/Utils.hpp"

using namespace std;
using namespace MinisatID;

SolverOption modes; //Used by parser, initialized before parsing!

string programInfo =
	"MinisatID is a model generator for the language ECNF, an extension of CNF with aggregates expressions"
	"(sum, cardinality, min, max and product) and inductive definitions.\n"
	"Several other well-known input formats are also supported:\n"
	"\t - ground LParse, used within the domain of answer-set programming.\n"
	"\t - QBF, used within the domain of quantified boolean formula reasoning.\n"
	"\t - OPB, used within the domain of pseudo-boolean constraint solving.\n\n"
	"MinisatID is part of the IDP system, a knowledge base system based on the language FO(.). IDP supports "
	"among others state-of-the-art model expansion inference.\n\n"
	"MinisatID is the courtesy of the Knowledge Representation and Reasoning (KRR) group at the K.U. Leuven, "
	"Belgium and is maintained by Broes De Cat. More information on the systems and the research can be found "
	"on \"http://dtai.cs.kuleuven.be/krr\".\n";
string programVersion = "2.2.0";

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

	NoValsOption(const string &s, const string &l, const string &m, const T& def, const string& type, T& modesarg, TCLAP::CmdLine& cmd):
		shortopt(s), longopt(l), mess(m), defaultval(def), modesarg(modesarg){

		arg = new TCLAP::ValueArg<T>(shortopt,longopt, mess, false, defaultval, type, cmd);
	};

	~NoValsOption(){
		delete arg;
	}

	void parse(){
		//cerr <<longopt <<" " <<arg->getValue() <<endl;
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

	Option(const string &s, const string &l, const string &m, const T& def, const vector<T>& vals, const vector<pair<T2, string> >& desc, T& modesarg, TCLAP::CmdLine& cmd):
		shortopt(s), longopt(l), mess(m), defaultval(def), vals(vals), desc(desc), modesarg(modesarg){
		vector<T2> constrvals;
		for(typename vector<pair<T2, string> >::const_iterator i=desc.begin(); i<desc.end(); i++){
			constrvals.push_back((*i).first);
		}
		formatsconstr = new TCLAP::ValuesConstraint<T2>(constrvals);

		stringstream ss;

		assert(desc.size()>0 && vals.size()==desc.size());
		T2 tclapdefault = desc[0].first;
		bool found = false;
		ss <<mess <<":" <<endl;
		for(typename vector<T>::size_type i=0; i<vals.size(); i++){
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
		for(; i<desc.size(); i++){
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
	string outputfile;

	vector<Opt*> options;

	vector<bool> yesnovals; //Maintain this order in desc vectors!
	yesnovals.push_back(true);
	yesnovals.push_back(false);

	vector<INPUTFORMAT> formatvals;
	vector<pair<string, string> > formatdesc;
	formatvals.push_back(FORMAT_FODOT); formatdesc.push_back(pair<string, string>("fodot", "propositional FO(.)"));
	formatvals.push_back(FORMAT_ASP); formatdesc.push_back(pair<string, string>("asp", "propositional LParse ASP"));
	formatvals.push_back(FORMAT_OPB); formatdesc.push_back(pair<string, string>("opb", "open pseudo-boolean"));

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

	TCLAP::CmdLine cmd = TCLAP::CmdLine(programInfo, '=', programVersion); //second arg is delimiter: -option<delim>value

	TCLAP::UnlabeledValueArg<string> inputfilearg("inputfile", "The file which contains the input theory. If not provided, the standard-in stream is assumed as input.", false, "", "inputfile", cmd);

	options.push_back(new NoValsOption<int>("n","nbmodels", "The number of models to search for.", 1,"int", modes.nbmodels, cmd));
	options.push_back(new NoValsOption<int>("","verbosity", "The level of output to generate.", 1,"int", modes.verbosity, cmd));
	options.push_back(new NoValsOption<long>("","ufsvarintro","Threshold (compared with ufssize*loopfsize) above which an extra variable is introduced when an unfounded set is found.", 500,"long", modes.ufsvarintrothreshold, cmd));
	options.push_back(new NoValsOption<double>("","rnd-freq","The frequency with which to make a random choice (between 0 and 1).", getDefaultRandfreq(),"double", modes.rand_var_freq, cmd));
	options.push_back(new NoValsOption<double>("","decay","The decay of variable activities within the SAT-solver (larger than or equal to 0).", getDefaultDecay(),"double", modes.var_decay, cmd));
	options.push_back(new NoValsOption<string>("o","outputfile","The outputfile to use to write out models.", "","file", outputfile, cmd));
	options.push_back(new NoValsOption<string>("","primesfile","File containing a list of prime numbers to use for finding optimal bases. Has to be provided if using pbsolver.", "","file", modes.primesfile, cmd));
	options.push_back(new Option<INPUTFORMAT, string>("f", "format", "The format of the input theory", FORMAT_FODOT, formatvals, formatdesc, modes.format, cmd));
	options.push_back(new Option<bool, string>("", "ecnfgraph", "Choose whether to generate a .dot graph representation of the ecnf", false, yesnovals, ecnfgraphdesc, modes.printcnfgraph, cmd));
	options.push_back(new Option<bool, string>("r", "remap", "Choose whether to remap literals from the input structure to a contiguous internal representation", true, yesnovals, remapdesc, modes.remap, cmd));
	options.push_back(new Option<bool, string>("","bumpagg","Choose whether to bump variable activity on aggregate propagation", true, yesnovals, bumpaggonnotifydesc, modes.bumpaggonnotify, cmd));
	options.push_back(new Option<bool, string>("","bumpid", "Choose whether to bump variable activity on ID initialization", true, yesnovals, bumpidonstartdesc, modes.bumpidonstart, cmd));
	options.push_back(new Option<bool, string>("","minimexplan", "Choose whether to minimize aggregate explanations", false, yesnovals, subsetminimdesc, modes.subsetminimizeexplanation, cmd));
	options.push_back(new Option<bool, string>("","asapaggprop", "Choose whether to propagate aggregates as fast as possible", false, yesnovals, asapaggpropdesc, modes.asapaggprop, cmd));
	options.push_back(new Option<bool, string>("","pbsolver","Choose whether to translate pseudo-boolean constraints to SAT", false, yesnovals, pbsolverdesc, modes.pbsolver, cmd));
#ifndef USEMINISAT22
	options.push_back(new Option<POLARITY, string>("","polarity", "The default truth value choice of variables", getDefaultPolarity(), polvals, poldesc, modes.polarity, cmd));
#endif
	options.push_back(new Option<int, int>("","aggsaving", "How to handle propagation reasons within Agg solver", 2, aggsavingvals, aggsavingdesc, modes.aggclausesaving, cmd));
	options.push_back(new Option<DEFFINDCS, string>("","defsearch","Choose the unfounded-set search-frequency", always, defsearchvals, defsearchdesc, modes.defn_strategy, cmd));
	options.push_back(new Option<DEFSEM, string>("","defsem","Choose the semantics of the inductive definitions", DEF_WELLF, defsemvals, defsemdesc, modes.defsem, cmd));
	options.push_back(new Option<int, int>("","idsaving", "Choose how to handle propagation reasons within ID solver", 0, idsavingvals, idsavingdesc, modes.idclausesaving, cmd));

	modes.ufs_strategy = breadth_first;
	modes.defn_search = include_cs;
	modes.selectOneFromUFS = false;
	modes.watchedagg = false;
	//TCLAP::ValueArg<string> 		watcharg("w","watchedagg",
	//		"Use | don't use watched-literal datastructures to handle aggregate propagation", false, "no", &getYesNoConstraint(), cmd);

	try {
		cmd.parse(argc, argv);
	} catch (TCLAP::ArgException &e){
		std::cerr << "Error: " << e.error() << " for arg " << e.argId() << std::endl;
		return false;
	}

	for(vector<Opt*>::const_iterator i=options.begin(); i<options.end(); i++){
		(*i)->parse();
	}

	if(modes.var_decay<0.0){
		report("The value for decay should be larger than 0.\n");
		return false;
	}
	if(modes.rand_var_freq<0.0 || modes.rand_var_freq>1.0){
		report("The value for rnd-freq should be between 0 and 1.\n");
		return false;
	}

	if(inputfilearg.isSet()){
		setInputFileUrl(inputfilearg.getValue());
	}
	if(outputfile.compare("")!=0){
		setOutputFileUrl(outputfile);
	}

	if(modes.pbsolver && modes.primesfile.compare("")==0){
		report("When using the pbsolver, a file containing prime numbers has to be supplied with \"--primesfile\"!\n");
		return false;
	}

	deleteList<Opt>(options);

	//cerr <<inputfilearg.getValue() <<endl;
	//modes.print();

	return true;
}
