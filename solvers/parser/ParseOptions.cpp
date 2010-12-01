/*
 * ParseOptions.cpp
 *
 *  Created on: Nov 29, 2010
 *      Author: broes
 */

#include "solvers/parser/ParseOptions.hpp"

#include <vector>
#include <string>
#include <tclap/CmdLine.h>
#include "solvers/external/ExternalUtils.hpp"

using namespace std;
using namespace MinisatID;

SolverOption modes; //Used by parser, initialized before parsing!

string programInfo =
	"Minisat-ID is courtesy of the KRR group at K.U. Leuven, Belgium, more info available on \"http://dtai.cs.kuleuven.be/krr\".\n"
	"MinisatID is a model expansion system for propositional logic extended with aggregates "
	"and inductive definitions. Also lparse and opb languages are supported.\n";
string programVersion = "2.1.21";
TCLAP::CmdLine cmd = TCLAP::CmdLine(programInfo, '=', programVersion); //second arg is delimiter: -option<delim>value

vector<string> yesnovals;
vector<string>& initYesNoVals(){
	yesnovals.push_back("yes");
	yesnovals.push_back("no");
	return yesnovals;
}
vector<string> formatvals;
vector<string>& initFormatVals(){
	formatvals.push_back("fodot");
	formatvals.push_back("asp");
	formatvals.push_back("opb");
	return formatvals;
}
vector<string> polarvals;
vector<string>& initPolarVals(){
	polarvals.push_back("true");
	polarvals.push_back("false");
	polarvals.push_back("rnd");
	return polarvals;
}
vector<int> aggsavingvals;
vector<int>& initAggSavingVals(){
	aggsavingvals.push_back(0);
	aggsavingvals.push_back(1);
	aggsavingvals.push_back(2);
	return aggsavingvals;
}
vector<string> defsearchvals;
vector<string>& initDefSearchVals(){
	defsearchvals.push_back("always");
	defsearchvals.push_back("adaptive");
	defsearchvals.push_back("lazy");
	return defsearchvals;
}
vector<string> defsemvals;
vector<string>& initDefSemVals(){
	defsemvals.push_back("stable");
	defsemvals.push_back("wellfounded");
	return defsemvals;
}
vector<int> idsavingvals;
vector<int>& initIDSavingVals(){
	idsavingvals.push_back(0);
	idsavingvals.push_back(1);
	return idsavingvals;
}

TCLAP::ValuesConstraint<string> yesnoconstr(initYesNoVals());
TCLAP::ValuesConstraint<string>& getYesNoConstraint(){
	return yesnoconstr;
}
bool parseYesNo(string chosenval){
	return chosenval.compare("yes")==0;
}

TCLAP::ValuesConstraint<string> formatsconstr( initFormatVals() );
TCLAP::ValueArg<std::string> 	formatarg("f","format",
		"The format of the input theory", false,"fodot",&formatsconstr, cmd);
TCLAP::ValueArg<int> 			modelarg("n","nbmodels",
		"The number of models to search for", false,1,"int", cmd);
TCLAP::ValueArg<int> 			verbosityarg("","verbosity",
		"The level of output to generate", false,1,"int", cmd);
TCLAP::ValueArg<string> 		ecnfgrapharg("","ecnfgraph",
		"Generate | don't generate .dot ecnf graph representation", false, "no", &getYesNoConstraint(), cmd);
TCLAP::UnlabeledValueArg<string> inputfilearg("inputfile",
		"The inputfile with a logical theory. Standard in is used if no provided.", false, "", "string", cmd);
TCLAP::ValueArg<std::string> 	outputfilearg("o","outputfile",
		"The outputfile to use to write out models", false, "","string", cmd);
TCLAP::ValueArg<double> 		rndfreqarg("","rnd-freq",
		"The frequency with which to make a random choice (between 0 and 1)", false,0.02,"double", cmd);
TCLAP::ValueArg<double> 		decayarg("","decay",
		"The decay of variable activities within the SAT-solver (between 0 and 1)", false,0.02,"double", cmd);
TCLAP::ValuesConstraint<string> polarconstr(polarvals);
TCLAP::ValueArg<std::string> 	polarityarg("","polarity-mode",
		"The default truth value choice of variables", false,"false",&polarconstr, cmd);
TCLAP::ValuesConstraint<int> 	aggsavingconstr(initAggSavingVals());
TCLAP::ValueArg<int> 			aggsavingarg("","aggsaving",
		"How to handle propagation reasons within Agg solver: add to theory on propagation (0), save clause on propagation (1), save reason on propagation (2)", false,2,&aggsavingconstr, cmd);
TCLAP::ValueArg<string> 		remaparg("r","remap",
		"Remap | don't remap literals from the input structure to a contiguous internal representation", false, "yes", &getYesNoConstraint(), cmd);
TCLAP::ValueArg<string> 		bumpaggonnotify("b","bump",
		"Bump | don't bump variable activity on aggregate propagation", false, "yes", &getYesNoConstraint(), cmd);
TCLAP::ValueArg<string> 		watcharg("w","watchedagg",
		"Use | don't use watched-literal datastructures to handle aggregate propagation", false, "no", &getYesNoConstraint(), cmd);
TCLAP::ValueArg<string> 		pbsolverarg("",
		"pbsolver","Use | don't use translation of pseud-boolean constraints to SAT", false, "no", &getYesNoConstraint(), cmd);
TCLAP::ValueArg<std::string> 	primesfilearg("",
		"primesfile","File containing a list of prime numbers to use for finding optimal bases. Has to be provided if using pbsolver.", false, "","string", cmd);
TCLAP::ValuesConstraint<string> defsearchconstr(initDefSearchVals());
TCLAP::ValueArg<string> 		defsearcharg("",
		"defsearch","sets the unfounded-set search-frequency", false, "always", &defsearchconstr, cmd);
TCLAP::ValuesConstraint<string> defsemconstr(initDefSemVals());
TCLAP::ValueArg<string> 		defsemarg("",
		"defsem","uses the chosen semantics to handle inductive definitions", false, "stable", &defsemconstr, cmd);
TCLAP::ValuesConstraint<int> 	idsavingconstr( initIDSavingVals() );
TCLAP::ValueArg<int> 			idsavingarg("","idsaving",
		"How to handle propagation reasons within ID solver: 0=add clause on propagation, 1=save clause on propagation", false,0,&idsavingconstr, cmd);

POLARITY getChosenPolarity(){
	if(polarityarg.getValue().compare("true")==0){
		return POL_TRUE;
	}else if(polarityarg.getValue().compare("false")==0){
		return POL_FALSE;
	}else{
		return POL_RAND;
	}
}
DEFFINDCS getChosenCSStrategy(){
	if(defsearcharg.getValue().compare("always")==0){
		return always;
	}else if(defsearcharg.getValue().compare("adaptive")==0){
		return adaptive;
	}else{
		return lazy;
	}
}
DEFSEM getChosenSemantics(){
	if(defsemarg.getValue().compare("stable")==0){
		return STABLE;
	}else{
		return WELLF;
	}
}

///////
// OPTION PARSING
///////

INPUTFORMAT MinisatID::getChosenFormat(){
	if(formatarg.getValue().compare("fodot")==0){
		return FORMAT_FODOT;
	}else if(formatarg.getValue().compare("asp")==0){
		return FORMAT_ASP;
	}else{
		return FORMAT_OPB;
	}
}

//Return false if parsing failed
bool MinisatID::parseOptions(int argc, char** argv){
	try {
		cmd.parse(argc, argv);
	} catch (TCLAP::ArgException &e){
		std::cerr << "Error: " << e.error() << " for arg " << e.argId() << std::endl;
		return false;
	}

	if(inputfilearg.isSet()){
		setInputFileUrl(inputfilearg.getValue().c_str());
	}
	if(outputfilearg.isSet()){
		setOutputFileUrl(outputfilearg.getValue().c_str());
	}

	//initialize options datastructure
	modes.aggclausesaving = aggsavingarg.getValue();
	modes.idclausesaving = idsavingarg.getValue();
	modes.defn_strategy = getChosenCSStrategy();
	modes.remap = parseYesNo(remaparg.getValue());
	modes.watchedagg = parseYesNo(watcharg.getValue());
	modes.pbsolver = parseYesNo(pbsolverarg.getValue());
	if(modes.pbsolver){
		if(!primesfilearg.isSet()){
			report("When using the pbsolver, a file containing prime numbers has to be supplied with \"--primesfile\"!\n");
			return false;
		}
		modes.primesfile = primesfilearg.getValue();
	}
	modes.printcnfgraph = parseYesNo(ecnfgrapharg.getValue());
	modes.verbosity = verbosityarg.getValue();
	modes.nbmodels = modelarg.getValue();
	modes.defsem = getChosenSemantics();
	modes.defn_search = include_cs;
	modes.selectOneFromUFS = false;
	if(decayarg.getValue()<0.0 || decayarg.getValue()>1.0){
		report("The value for decay should be between 0 and 1.\n");
		return false;
	}
	modes.var_decay = decayarg.getValue();
	if(rndfreqarg.getValue()<0.0 || rndfreqarg.getValue()>1.0){
		report("The value for rnd-freq should be between 0 and 1.\n");
		return false;
	}
	modes.rand_var_freq = rndfreqarg.getValue();
	modes.polarity = getChosenPolarity();
	modes.bumpaggonnotify = parseYesNo(bumpaggonnotify.getValue());

	return true;
}
