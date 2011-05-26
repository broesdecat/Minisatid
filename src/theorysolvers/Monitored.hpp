#include <vector>

#include "utils/Utils.hpp"
#include "external/SolvingMonitor.hpp"

namespace MinisatID{
class Monitored{
private:
	std::vector<Monitor*> monitors;

public:
	void requestMonitor(MinisatID::Monitor* monitor) { monitors.push_back(monitor); }

	bool isBeingMonitored() const { return monitors.size()>0; }

	void notifyMonitor(const MinisatID::InnerPropagation& obj){
		for(std::vector<MinisatID::Monitor*>::const_iterator i=monitors.begin(); i<monitors.end(); ++i){
			(*i)->notifyPropagated(obj.propagation, obj.decisionlevel);
		}
	}

	void notifyMonitor(const InnerBacktrack& obj){
		for(std::vector<MinisatID::Monitor*>::const_iterator i=monitors.begin(); i<monitors.end(); ++i){
			(*i)->notifyBacktracked(obj.untillevel);
		}
	}
};
}
