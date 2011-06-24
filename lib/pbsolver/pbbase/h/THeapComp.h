#ifndef THEAPCOMP_H_
#define THEAPCOMP_H_

#include <vector>
#include "../h/BaseSearchStateRelativeComp.h"

namespace MiniSatPP {
	
typedef struct BaseSearchStateRelativeComp* bssr;

class THeapComp {
	
  public:
  
	THeapComp();
	virtual ~THeapComp();
	bool offer(bssr element);
	bool isEmpty();
	bssr peek();	
	bssr poll();
	void update(bssr inQue);
	
	
  private:
   
    std::vector<bssr> heap;
  	void siftUp(int index);
	void siftDown(int index);
};

}       

#endif /*THEAPCOMP_H_*/
