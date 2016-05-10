/* 
 * File:   ModelIterationTask.hpp
 * Author: rupsbant
 *
 * Created on November 19, 2014, 6:11 PM
 */

#pragma once

#include "Options.hpp"
#include "Datastructures.hpp"
#include "MXStatistics.hpp"
#include <vector>
#include <memory>

namespace MinisatID {

    class ModelManager;
    class Printer;
    class Space;
    class SearchEngine;
    
    typedef std::vector<Lit> litlist;

    class ModelIterationTask {
    public:
        ModelIterationTask(Space* space, ModelExpandOptions options, const litlist& assumptions);
        ModelIterationTask(const ModelIterationTask& orig);
        virtual ~ModelIterationTask();
        MXStatistics getStats() const;
        
        void initialise();
        std::shared_ptr<Model> findNext();
        void notifyTerminateRequested();

        void addAssumption(Atom, bool);
        void removeAssumption(Atom, bool);
        void addClause(const std::vector<std::pair<unsigned int,bool> >& lits);  // unsigned int is IDP atom (but sign is gone already)
        void getOutOfUnsat();

    private:
        SolverOption modes;

        Space* space;
        
	ModelExpandOptions _options;
	litlist assumptions; // Note: internal literals

	ModelManager* _solutions; 
	Printer* printer;
        bool terminated;
        bool modelsFound;
        
        bool terminateRequested() const {
            return terminated;
        }

        const SolverOption& getOptions() const {
            return modes;
        }

        Space* getSpace() const {
            return space;
        }
        SearchEngine& getSolver() const;
        
        std::shared_ptr<Model> findNextModel();
	
	void notifySolvingAborted();
        
	void invalidate(litlist& clause);
        SATVAL invalidateModel();
	SATVAL invalidateModel(Disjunction& clause);
    };

}

