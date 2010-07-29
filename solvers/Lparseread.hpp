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

using namespace std;

#include "solvers/ExternalInterface.hpp"

struct GenRule{
	long atleast;
	vector<Literal> heads;
	vector<Literal> body;

	GenRule(long atleast, vector<Literal>& heads, vector<Literal>& body):atleast(atleast), heads(heads), body(body){

	}
};

struct ChoiceRule{
	vector<Literal> heads;
	vector<Literal> body;

	ChoiceRule(vector<Literal>& heads, vector<Literal>& body): heads(heads), body(body){

	}
};

class Read{
public:
	Read (PropositionalSolver* solver);
	~Read ();
	int read (istream &f);

private:
	int readBody (istream &f, long size, bool pos, vector<Literal>& body);
	int addBasicRule (istream &f);
	int addConstraintRule (istream &f);
	int addGenerateRule (istream &f);
	int addChoiceRule (istream &f);
	int addWeightRule (istream &f);
	int addOptimizeRule (istream &f);

	Literal makeLiteral(int n, bool sign);
	int finishGenerateRules();
	int finishChoiceRules();

	int maxatomnumber;
	int setcount;
	long size;
	long linenumber;
	PropositionalSolver* solver;
	PropositionalSolver* getSolver() { return solver; }

	vector<GenRule> genrules;
	vector<ChoiceRule> choicerules;
};

#endif
