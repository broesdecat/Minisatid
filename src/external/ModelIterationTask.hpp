/* 
 * File:   ModelIterationTask.hpp
 * Author: rupsbant
 *
 * Created on November 19, 2014, 6:11 PM
 */

#ifndef MODELITERATIONTASK_HPP
#define	MODELITERATIONTASK_HPP

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
    private:
        bool terminated = false;
        bool modelsFound = false;
        SolverOption modes;

        Space* space;
        
	ModelExpandOptions _options;
	litlist assumptions; // Note: internal literals

	ModelManager* _solutions; 
	Printer* printer;
        
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
#endif	/* MODELITERATIONTASK_HPP */

