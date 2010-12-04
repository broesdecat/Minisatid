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
	"MinisatID is a model generator for propositional logic extended with aggregates "
	"and inductive definitions. Also lparse and opb languages are supported.\n"
	"MinisatID is part of the IDP system, a knowledge base system using extended first-order logic "
	"and supports among others state-of-the-art model expansion inference.\n"
	"MinisatID is the courtesy of the Knowledge Representation and Reasoning (KRR) group at the Katholic University of Leuven in"
	"Belgium. More information on the systems and the research are available on \"http://dtai.cs.kuleuven.be/krr\".\n";
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
	polarvals.push_back("rand");
	polarvals.push_back("user");
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
		"The file which contains the input theory. If not provided, the standard-in stream is assumed as input.", false, "", "string", cmd);
TCLAP::ValueArg<std::string> 	outputfilearg("o","outputfile",
		"The outputfile to use to write out models", false, "","string", cmd);
TCLAP::ValueArg<double> 		rndfreqarg("","rnd-freq",
		"The frequency with which to make a random choice (between 0 and 1)", false,0.02,"double", cmd);
TCLAP::ValueArg<double> 		decayarg("","decay",
		"The decay of variable activities within the SAT-solver (larger than or equal to 0)", false,1/0.95,"double", cmd);
TCLAP::ValuesConstraint<string> polarconstr(initPolarVals());
TCLAP::ValueArg<std::string> 	polarityarg("","polarity",
		"The default truth value choice of variables", false,"user",&polarconstr, cmd);
TCLAP::ValuesConstraint<int> 	aggsavingconstr(initAggSavingVals());
TCLAP::ValueArg<int> 			aggsavingarg("","aggsaving",
		"How to handle propagation reasons within Agg solver: add to theory on propagation (0), save clause on propagation (1), save reason on propagation (2)", false,2,&aggsavingconstr, cmd);
TCLAP::ValueArg<string> 		remaparg("r","remap",
		"Remap | don't remap literals from the input structure to a contiguous internal representation", false, "yes", &getYesNoConstraint(), cmd);
TCLAP::ValueArg<string> 		bumpaggonnotifyarg("","bumpagg",
		"Bump | don't bump variable activity on aggregate propagation", false, "yes", &getYesNoConstraint(), cmd);
TCLAP::ValueArg<string> 		bumpidonstartarg("","bumpid",
		"Bump | don't bump variable activity on ID initialization", false, "yes", &getYesNoConstraint(), cmd);
TCLAP::ValueArg<string> 		subsetminimizeexplanationarg("","minimexplan",
		"Minimize | don't minimize explanations", false, "no", &getYesNoConstraint(), cmd);
TCLAP::ValueArg<string> 		asapaggproparg("","asapaggprop",
		"Propagate aggregates as fast as possible", false, "no", &getYesNoConstraint(), cmd);
TCLAP::ValueArg<long>	 		ufsvarintrothresholdarg("","ufsvarintro",
		"Threshold (compared with ufssize*loopfsize) above which an extra variable is introduced when unfounded sets are found", false, 500, "long", cmd);
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
	}else if(polarityarg.getValue().compare("rand")==0){
		return POL_RAND;
	}else{
		return POL_USER;
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
	if(decayarg.getValue()<0.0){
		report("The value for decay should be larger than 0.\n");
		return false;
	}
	modes.var_decay = decayarg.getValue();
	if(rndfreqarg.getValue()<0.0 || rndfreqarg.getValue()>1.0){
		report("The value for rnd-freq should be between 0 and 1.\n");
		return false;
	}
	modes.rand_var_freq = rndfreqarg.getValue();
	modes.polarity = getChosenPolarity();
	modes.bumpaggonnotify = parseYesNo(bumpaggonnotifyarg.getValue());
	modes.bumpidonstart = parseYesNo(bumpidonstartarg.getValue());
	modes.subsetminimizeexplanation = parseYesNo(subsetminimizeexplanationarg.getValue());
	modes.asapaggprop = parseYesNo(asapaggproparg.getValue());

	modes.ufsvarintrothreshold = ufsvarintrothresholdarg.getValue();

	return true;
}
