#include <vector>
#include "../h/BaseSearchStateRelativeComp.h"
#include "../h/THeapComp.h"


namespace MiniSatPP {
	
typedef struct BaseSearchStateRelativeComp* bssr;

#define smallerThen(x,y) relComp(x->hCnfSize,x->carryCost,y->hCnfSize,y->carryCost)
#define svmComp(a,b)     svm_predict(model,toSVMVector(a,b))
  
	THeapComp::THeapComp() {}
	
	THeapComp::~ THeapComp() {
		for (unsigned int i=0;i<heap.size();i++)
			delete heap[i];
	};

	bool THeapComp::offer(bssr element) {
		heap.push_back(element);
		element->index = heap.size() - 1;
		siftUp(heap.size()-1);
		return 1;
	}
	
	/**
	 * @pre assumes the hcost of inQue was reducet prior to to call;
	 */
	void  THeapComp::update(bssr inQue) {
		siftUp(inQue->index);
	}
	
	bool THeapComp::isEmpty(){
		return 0==heap.size();
	}
	
	bssr THeapComp::peek(){		
		return heap[0];
	}

	
	bssr THeapComp::poll(){
		switch(heap.size()) {
			case 0: return 0;
            case 1: {
                    bssr min1 = heap[0];
					heap.pop_back();
					return min1;
            }
			default:
					bssr min = heap[0];
					heap[0] = heap[heap.size() - 1];
					heap[0]->index = 0;
					heap.pop_back();
					siftDown(0);
					return min;
		}
	}
	
	
	void THeapComp::siftUp(int index) {
		int parent = (index - 1) / 3;
		while(index > 0 && smallerThen(heap[index],heap[parent])) {
			bssr temp = heap[index];
			heap[index] = heap[parent];
			heap[parent] = temp;
			heap[index]->index = index;
			heap[parent]->index = parent;
			index = parent;
			parent = (index - 1) / 3;
		}
	}

	void THeapComp::siftDown(int index) {
		do {
			int left = 3 * index + 1;
			int middle = left + 1;
			int right = middle + 1;
			int min = index;
			int size = heap.size();
			if (left < size && smallerThen(heap[left],heap[index])) 
					min = left;
			if(middle < size && smallerThen(heap[middle],heap[min])) 
					min = middle;
			if(right < size && smallerThen(heap[right],heap[min])) 
					min = right;
			if (min == index) break;
			bssr temp = heap[index];
			heap[index] = heap[min];
			heap[min] = temp;
			heap[index]->index = index;
			heap[min]->index = min;
			index = min;
		} while(true);
	}
	
}
