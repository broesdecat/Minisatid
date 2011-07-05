/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */

#include "gtest/gtest.h"

#include "utils/SCC.hpp"
#include "utils/Utils.hpp"

using namespace std;
using namespace MinisatID;

namespace Tests{

	struct Node{
		Node* parent;
		int id;
		int _scc;

		int& scc() { return _scc; }
	};

	struct Graph{
		vector<Node*> nodes;
	};

	int getID(Node* n){
		return n->id;
	}

	template<class Node, class Graph>
	class TrivialPolicy{
	private:
		int index;
		const Graph& graph;
	public:
		TrivialPolicy(const Graph& info): index(0), graph(info){}
		int getMaxElem() const {
			int max=0;
			for(typename vector<Node>::const_iterator i=graph.nodes.begin(); i<graph.nodes.end(); ++i){
				if((*i)->id>max){
					max = (*i)->id;
				}
			}
			return max;
		}

		bool hasNextNode() { return index<graph.nodes.size(); }
		Node getNextNode() { return graph.nodes[index++]; }

		bool isThroughNegative(Node) { return false; }

		void addChildNodes(Node v, vector<Node>& tovisit) {
			for(typename vector<Node>::const_iterator i=graph.nodes.begin(); i<graph.nodes.end(); ++i){
				if((*i)->parent==v){
					tovisit.push_back(*i);
				}
			}
		}
	};

	TEST(SCCTest, Trivial) {
		Graph g;
		Node *n1 = new Node(), *n2 = new Node();
		n1->id = 1;
		n1->parent = n2;
		n2->id = 2;
		n2->parent = n1;
		g.nodes.push_back(n1);
		g.nodes.push_back(n2);
		SCC<TrivialPolicy, Node*, Graph>* genscc = new SCC<TrivialPolicy, Node*, Graph>(g);
		genscc->visitAll();

/*	  // This test is named "Negative", and belongs to the "FactorialTest"
	  // test case.
	  EXPECT_EQ(1, Factorial(-5));
	  EXPECT_EQ(1, Factorial(-1));
	  EXPECT_TRUE(Factorial(-10) > 0);*/
	}

	TEST(FactorialTest, Zero) {
	}

}


int main(int argc, char **argv) {
  ::testing::InitGoogleTest(&argc, argv);
  return RUN_ALL_TESTS();
}
