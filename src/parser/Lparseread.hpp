//--------------------------------------------------------------------------------------------------
//    Copyright (c) 2009-2010, Broes De Cat, K.U.Leuven, Belgium
//    
//    Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
//    associated documentation files (the "Software"), to deal in the Software without restriction,
//    including without limitation the rights to use, copy, modify, merge, publish, distribute,
//    sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
//    furnished to do so, subject to the following conditions:
//    
//    The above copyright notice and this permission notice shall be included in all copies or
//    substantial portions of the Software.
//    
//    THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
//    NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
//    NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
//    DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
//    OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
//--------------------------------------------------------------------------------------------------

// Copyright 1998 by Patrik Simons
// This program is free software; you can redistribute it and/or
// modify it under the terms of the GNU General Public License
// as published by the Free Software Foundation; either version 2
// of the License, or (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program; if not, write to the Free Software
// Foundation, Inc., 59 Temple Place - Suite 330, Boston,
// MA 02111-1307, USA.
//
// Patrik.Simons@hut.fi
#ifndef READ_H
#define READ_H

#include "external/ExternalInterface.hpp"

namespace MinisatID {

class WrappedLogicSolver;
class LParseTranslator;

struct BasicRule{
	Literal head;
	std::vector<Literal> body;
	bool conj;

	BasicRule(Literal head, std::vector<Literal>& body, bool conj = true):head(head), body(body), conj(conj){	}
};

struct CardRule: public BasicRule{
	int setcount;
	Weight atleast;
	//Card, UB, DEF

	CardRule(int setcount, Literal head, std::vector<Literal>& body, const Weight& atleast):
			BasicRule(head, body), setcount(setcount), atleast(atleast){	}
};

struct SumRule: public BasicRule{
	int setcount;
	std::vector<Weight> weights;
	Weight atleast;
	//Sum, UB, DEF

	SumRule(int setcount, Literal head, std::vector<Literal>& body, std::vector<Weight> weights, const Weight& atleast):
		BasicRule(head, body), setcount(setcount), weights(weights), atleast(atleast){	}
};

struct ChoiceRule{
	std::vector<Literal> heads;
	std::vector<Literal> body;

	ChoiceRule(std::vector<Literal>& heads, std::vector<Literal>& body):heads(heads), body(body){	}
};

class Read{
private:
	bool endedparsing;
	int maxatomnumber;
	int setcount;
	long size;
	long linenumber;
	MinisatID::WrappedPCSolver* solver;

	std::vector<BasicRule*> basicrules;
	std::vector<CardRule*> cardrules;
	std::vector<SumRule*> sumrules;
	std::vector<ChoiceRule*> choicerules;

	std::map<Atom, bool> defatoms;

	bool optim;
	int optimsetcount;
	std::vector<Literal> optimbody;
	std::vector<Weight> optimweights;

	MinisatID::LParseTranslator* translator;

public:
	Read (WrappedPCSolver* solver);
	~Read ();
	bool read (std::istream &f);

private:
	bool readBody			(std::istream &f, long size, bool pos, std::vector<Literal>& body);
	bool readFullBody		(std::istream &f, std::vector<Literal>& body);
	bool readWeights		(std::istream &f, std::vector<Weight>& body, int bodysize);
	bool parseBasicRule		(std::istream &f);
	bool parseConstraintRule(std::istream &f);
	bool parseChoiceRule	(std::istream &f);
	bool parseWeightRule	(std::istream &f);
	bool parseOptimizeRule	(std::istream &f);

	Atom makeNewAtom		();
	Atom makeParsedAtom		(int n);
	Atom makeAtom			(int n);

	bool addBasicRules		();
	bool addCardRules		();
	bool addSumRules		();
	bool addOptimStatement	();
	bool tseitinizeHeads	();
	void addRuleToHead(std::map<Atom, std::vector<BasicRule*> >& headtorules, BasicRule* rule, Atom head);

	MinisatID::WrappedPCSolver* getSolver() { return solver; }
};

}

#endif
