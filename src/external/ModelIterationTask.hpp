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
#include "space/SearchEngine.hpp"
#include <vector>

namespace MinisatID {

    class ModelManager;
    class Printer;
    class Space;

    typedef std::vector<Lit> litlist;

    enum class MXState {
        MODEL, MODEL_FINAL, UNSAT, UNKNOWN
    };

    class ModelIterationTask {
    public:
        ModelIterationTask(Space* space, ModelExpandOptions options, const litlist& assumptions);
        ModelIterationTask(const ModelIterationTask& orig);
        virtual ~ModelIterationTask();
        MXStatistics getStats() const;
    private:
        bool terminate;
        SolverOption modes;
        virtual void notifyTerminateRequested();

        Space* space;
        
	ModelExpandOptions _options;
	litlist assumptions; // Note: internal literals
        MXState state = MXState::MODEL;
    protected:

        bool terminateRequested() const {
            return terminate;
        }

        const SolverOption& getOptions() const {
            return modes;
        }

        Space* getSpace() const {
            return space;
        }
        SearchEngine& getSolver() const;
        
        //???
        void initialise();
        const modellist& getSolutions() const;
	
	bool isSat() const;
	bool isUnsat() const;
	void notifySolvingAborted();
        
        MXState findNext();
	void invalidate(litlist& clause);
        SATVAL invalidateModel();
	SATVAL invalidateModel(Disjunction& clause);

	litlist savedinvalidation;

	ModelManager* _solutions; 
	Printer* printer;
    };

}
#endif	/* MODELITERATIONTASK_HPP */

