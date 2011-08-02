#ifndef THEAP_H_
#define THEAP_H_

#include <vector>
#include "../h/BaseSearchState.h"

namespace MiniSatPP {
	
typedef struct BaseSearchState* bss;

class THeap {
	
  public:
  
	THeap();
	virtual ~THeap();
	bool offer(bss element);
	bool isEmpty();
	bss peek();	
	bss poll();
	void update(bss inQue);
	
	
  private:
   
    std::vector<bss> heap;
  	void siftUp(int index);
	void siftDown(int index);
};  

}     

#endif /*THEAP_H_*/
