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

#include "solvers/external/ExternalInterface.hpp"

namespace MinisatID {

struct BasicRule{
	Literal head;
	std::vector<Literal> body;

	BasicRule(Literal head, std::vector<Literal>& body):head(head), body(body){	}
};

struct CardRule{
	int setcount;
	Literal head;
	std::vector<Literal> body;
	int atleast;
	//Card, UB, DEF

	CardRule(int setcount, Literal head, std::vector<Literal>& body, int atleast):
			setcount(setcount), head(head), body(body), atleast(atleast){	}
};

struct SumRule{
	int setcount;
	Literal head;
	std::vector<Literal> body;
	std::vector<Weight> weights;
	int atleast;
	//Card, UB, DEF

	SumRule(int setcount, Literal head, std::vector<Literal>& body, std::vector<Weight> weights, int atleast):
			setcount(setcount), head(head), body(body), weights(weights), atleast(atleast){	}
};

struct GenRule{
	long atleast;
	std::vector<Literal> heads;
	std::vector<Literal> body;

	GenRule(long atleast, std::vector<Literal>& heads, std::vector<Literal>& body):
			atleast(atleast), heads(heads), body(body){	}
};

struct ChoiceRule{
	std::vector<Literal> heads;
	std::vector<Literal> body;

	ChoiceRule(std::vector<Literal>& heads, std::vector<Literal>& body): heads(heads), body(body){}
};

class Read{
public:
	Read (PropositionalSolver* solver);
	~Read ();
	int read (std::istream &f);

private:
	int readBody (std::istream &f, long size, bool pos, std::vector<Literal>& body);
	int addBasicRule (std::istream &f);
	int addConstraintRule (std::istream &f);
	int addGenerateRule (std::istream &f);
	int addChoiceRule (std::istream &f);
	int addWeightRule (std::istream &f);
	int addOptimizeRule (std::istream &f);

	Literal makeLiteral(int n, bool sign);

	int finishBasicRules();
	int finishCardRules();
	int finishSumRules();
	int finishGenerateRules();
	int finishChoiceRules();

	int maxatomnumber;
	int setcount;
	long size;
	long linenumber;
	PropositionalSolver* solver;
	PropositionalSolver* getSolver() { return solver; }

	std::vector<BasicRule> basicrules;
	std::vector<CardRule> cardrules;
	std::vector<SumRule> sumrules;
	std::vector<GenRule> genrules;
	std::vector<ChoiceRule> choicerules;
};

}

#endif
