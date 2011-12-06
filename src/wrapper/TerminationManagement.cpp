#include "external/TerminationManagement.hpp"
bool terminationrequested = false;
void startInference(){
	terminationrequested = false;
}
bool terminateRequested(){
	return terminationrequested;
}
void requestTermination(){
	terminationrequested = true;
}
