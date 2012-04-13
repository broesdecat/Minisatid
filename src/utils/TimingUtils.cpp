#include "external/utils/TimingUtils.hpp"
#include <ctime>

namespace MinisatID {
	//In elapsed seconds, taking abstraction of other processes running on the system
	double cpuTime(void) {
		return (double)clock() / CLOCKS_PER_SEC;
	}
}
