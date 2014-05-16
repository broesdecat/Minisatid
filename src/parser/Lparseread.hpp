/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */

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
#pragma once

#include "external/Translator.hpp"
#include "utils/Utils.hpp"

namespace MinisatID {

class WrappedLogicSolver;

struct BasicRule{
	Atom head;
	std::vector<Lit> body;
	bool conj;

	BasicRule(const Atom& head, std::vector<Lit>& body, bool conj = true):head(head), body(body), conj(conj){	}
};

struct CardRule: public BasicRule{
	int setcount;
	Weight atleast;
	//Card, UB, DEF

	CardRule(int setcount, const Atom& head, std::vector<Lit>& body, const Weight& atleast):
			BasicRule(head, body), setcount(setcount), atleast(atleast){	}
};

struct SumRule: public BasicRule{
	int setcount;
	std::vector<Weight> weights;
	Weight atleast;
	//Sum, UB, DEF

	SumRule(int setcount, const Atom& head, std::vector<Lit>& body, std::vector<Weight> weights, const Weight& atleast):
		BasicRule(head, body), setcount(setcount), weights(weights), atleast(atleast){	}
};

struct ChoiceRule{
	std::vector<Atom> heads;
	std::vector<Lit> body;

	ChoiceRule(std::vector<Atom>& heads, std::vector<Lit>& body):heads(heads), body(body){	}
};

template<class T>
class Read{
private:
	bool endedparsing;
	int maxatomnumber;
	int setcount;
	long size;
	long linenumber;
	int defaultdefinitionID;
	T& solver;

	std::vector<BasicRule*> basicrules;
	std::vector<CardRule*> cardrules;
	std::vector<SumRule*> sumrules;
	std::vector<ChoiceRule*> choicerules;

	std::map<Atom, bool> defatoms;

	bool optim;
	int optimsetcount;
	std::vector<Lit> optimbody;
	std::vector<Weight> optimweights;

	MinisatID::LParseTranslator* translator;

public:
	Read(T& solver, LParseTranslator* trans):
		endedparsing(false),
		maxatomnumber(1), setcount(1), size(0), defaultdefinitionID(1),
		solver(solver), optim(false),
		translator(trans){
	}
	~Read ();
	bool read (std::istream &f);

private:
	bool readBody			(std::istream &f, long size, bool pos, std::vector<Lit>& body);
	bool readFullBody		(std::istream &f, std::vector<Lit>& body);
	bool readWeights		(std::istream &f, std::vector<Weight>& body, int bodysize);
	bool parseBasicRule		(std::istream &f);
	bool parseConstraintRule(std::istream &f);
	bool parseChoiceRule	(std::istream &f);
	bool parseWeightRule	(std::istream &f);
	bool parseOptimizeRule	(std::istream &f);

	Atom makeNewAtom		();
	Atom makeParsedAtom		(int n);
	Atom makeAtom			(int n);

	void addBasicRules		();
	void addCardRules		();
	void addSumRules		();
	void addOptimStatement	();
	void tseitinizeHeads	();
	void addRuleToHead(std::map<Atom, std::vector<BasicRule*> >& headtorules, BasicRule* rule, Atom head);

	T& getSolver() { return solver; }
};

}
