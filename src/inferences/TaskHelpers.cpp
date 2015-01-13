/* 
 * File:   TaskHelpers.cpp
 * Author: rupsbant
 * 
 * Created on November 20, 2014, 9:49 AM
 */

#include "TaskHelpers.hpp"
using namespace std;
namespace MinisatID{
	//Translate into original vocabulary

	std::vector<Lit> getBackMappedModel(const std::vector<Lit>& model, const Remapper& r) {
		vector<Lit> outmodel;
		for (auto lit : model) {
			if (r.wasInput(lit)) {
				outmodel.push_back(r.getLiteral(lit));
			}
		}
		sort(outmodel.begin(), outmodel.end());
		return outmodel;
	}

	std::vector<VariableEqValue> getBackMappedModel(const std::vector<VariableEqValue>& model, const Remapper& r) {
		vector<VariableEqValue> outmodel;
		for (auto vareq : model) {
			if (r.wasInput(vareq.getVariable())) {
				auto image = vareq.hasValue();
				outmodel.push_back({r.getOrigID(vareq.getVariable()), image ? vareq.getValue() : 0, image});
			}
		}
		return outmodel;
	}

	void addModelToSolution(const std::shared_ptr<Model>& model, const Remapper& remapper, ModelManager& solution, Printer& printer) {
		auto outmodel = createModel(model, remapper);
		solution.addModel(outmodel);
		printer.addModel(outmodel);
	}

	Model* createModel(const std::shared_ptr<Model>& model, const Remapper& remapper) {
		auto outmodel = new Model();
		outmodel->literalinterpretations = getBackMappedModel(model->literalinterpretations, remapper);
		outmodel->variableassignments = getBackMappedModel(model->variableassignments, remapper);
		return outmodel;
	}
}