#include <vector>
#include "../h/BaseSearchState.h"
#include "../h/THeap.h"


namespace MiniSatPP {
	
typedef struct BaseSearchState* bss;

	THeap::THeap() {}
	
	THeap::~ THeap() {
		for (unsigned int i=0;i<heap.size();i++)
			delete heap[i];
	};

	bool THeap::offer(bss element) {
		heap.push_back(element);
		element->index = heap.size() - 1;
		siftUp(heap.size()-1);
		return 1;
	}
	
	/**
	 * @pre assumes the hcost of inQue was reducet prior to to call;
	 */
	void  THeap::update(bss inQue) {
		siftUp(inQue->index);
	}
	
	bool THeap::isEmpty(){
		return 0==heap.size();
	}
	
	bss THeap::peek(){		
		return heap[0];
	}

	
	bss THeap::poll(){
		switch(heap.size()) {
			case 0: return 0;
            case 1: {
                    bss min1 = heap[0];
					heap.pop_back();
					return min1;
            }
			default:
					bss min = heap[0];
					heap[0] = heap[heap.size() - 1];
					heap[0]->index = 0;
					heap.pop_back();
					siftDown(0);
					return min;
		}
	}
	
	
	void THeap::siftUp(int index) {
		int parent = (index - 1) / 3;
		while(index > 0 && heap[index]->hCost < heap[parent]->hCost) {
			bss temp = heap[index];
			heap[index] = heap[parent];
			heap[parent] = temp;
			heap[index]->index = index;
			heap[parent]->index = parent;
			index = parent;
			parent = (index - 1) / 3;
		}
	}

	void THeap::siftDown(int index) {
		do {
			int left = 3 * index + 1;
			int middle = left + 1;
			int right = middle + 1;
			int min = index;
			int size = heap.size();
			if (left < size && heap[left]->hCost < heap[index]->hCost) 
					min = left;
			if(middle < size && heap[middle]->hCost < heap[min]->hCost) 
					min = middle;
			if(right < size && heap[right]->hCost < heap[min]->hCost) 
					min = right;
			if (min == index) break;
			bss temp = heap[index];
			heap[index] = heap[min];
			heap[min] = temp;
			heap[index]->index = index;
			heap[min]->index = min;
			index = min;
		} while(true);
	}
}
	
	
