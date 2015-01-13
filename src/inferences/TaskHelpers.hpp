/* 
 * File:   TaskHelpers.hpp
 * Author: rupsbant
 *
 * Created on November 20, 2014, 9:49 AM
 */

#pragma once

#include <vector>
#include "space/Remapper.hpp"
#include "Printer.hpp"
#include "ModelManager.hpp"
#include "external/Datastructures.hpp"
namespace MinisatID {
    
    std::vector<Lit> getBackMappedModel(const std::vector<Lit>&, const Remapper&);
    std::vector<VariableEqValue> getBackMappedModel(const std::vector<VariableEqValue>&, const Remapper&);
    void addModelToSolution(const std::shared_ptr<Model>&, const Remapper&, ModelManager&, Printer&);
    Model* createModel(const std::shared_ptr<Model>&, const Remapper&);
}

