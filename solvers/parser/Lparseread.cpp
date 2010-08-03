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
#include <iostream>
#include <float.h>
#include <limits.h>
#include <string.h>
#include "solvers/parser/Lparseread.hpp"


typedef enum {
  ENDRULE,
  BASICRULE,
  CONSTRAINTRULE,
  CHOICERULE,
  GENERATERULE,
  WEIGHTRULE,
  OPTIMIZERULE
} RuleType;

Read::Read (PropositionalSolver* solver): solver(solver), size(0), setcount(1), maxatomnumber(1){
}

Read::~Read (){
}

Literal Read::makeLiteral(int n, bool sign = false){
	if(maxatomnumber<n){
		maxatomnumber = n;
	}
	return Literal(n, sign);
}

int Read::readBody (istream &f, long size, bool pos, vector<Literal>& body){
	long n;
	for (long i = 0; i < size; i++){
		f >> n;
		if (!f.good () || n < 1){
			cerr << "atom out of bounds, line " << linenumber << endl;
			return 1;
		}
		body.push_back(makeLiteral(n, !pos));
	}
	return 0;
}

int Read::addBasicRule (istream &f){
	long n;

	// Rule head
	f >> n;
	if (!f.good () || n < 1){
		cerr << "head atom out of bounds, line " << linenumber << endl;
		return 1;
	}
	Atom head(n);

	// Body
	f >> n;
	if (!f.good () || n < 0){
		cerr << "total body size, line " << linenumber << endl;
		return 1;
	}
	long bodysize = n;
	vector<Literal> body;

	// Negative body size
	f >> n;
	if (!f.good () || n < 0 || n > bodysize){
		cerr << "negative body size, line " << linenumber << endl;
		return 1;
	}
	long negbodysize = n;

	// Negative body
	if (readBody (f, negbodysize, false, body)){
		return 1;
	}
	// Positive body
	if (readBody (f, bodysize-negbodysize, true, body)){
		return 1;
	}

	if(!getSolver()->addRule(true, head, body)){
		return 1;
	}

	return 0;
}

int Read::addConstraintRule (istream &f){
	long n;

	// Rule head
	f >> n;
	if (!f.good () || n < 1){
		cerr << "head atom out of bounds, line " << linenumber << endl;
		return 1;
	}
	Atom head(n);

	// Body
	f >> n;
	if (!f.good () || n < 0){
		cerr << "total body size, line " << linenumber << endl;
		return 1;
	}
	long bodysize = n;
	vector<Literal> body;

	// Negative body size
	f >> n;
	if (!f.good () || n < 0 || n > bodysize){
		cerr << "negative body size, line " << linenumber << endl;
		return 1;
	}
	long negbodysize = n;

	// Choose
	f >> n;
	if (!f.good () || n < 0 || n > bodysize){
		return 1;
	}
	long atleast = n;

	// Negative body
	if (readBody (f, negbodysize, false, body)){
		return 1;
	}
	// Positive body
	if (readBody (f, bodysize-negbodysize, true, body)){
		return 1;
	}

	if(!getSolver()->addSet(setcount, body)){
		return 1;
	}
	if(!getSolver()->addAggrExpr(head, setcount, atleast, false, CARD, true)){
		return 1;
	}
	setcount++;

	return 0;
}

int Read::addGenerateRule (istream &f){
	long n;

	// Heads
	f >> n;
	if (!f.good () || n < 2){
		cerr << "head size less than two, line " << linenumber << endl;
		return 1;
	}
	long headssize = n;

	// choose
	f >> n;
	if (!f.good () || n <= 0 || n > headssize-1){
		cerr << "choose out of bounds, line " << linenumber << endl;
		return 1;
	}
	long atleast = n;


	vector<Literal> heads;
	for (long i = 0; i < headssize; i++){
		f >> n;
		if (!f.good () || n < 1){
			cerr << "atom out of bounds, line " << linenumber << endl;
			return 1;
		}
		heads.push_back(makeLiteral(n));
	}

	// Body
	f >> n;
	if (!f.good () || n < 0){
		cerr << "total body size, line " << linenumber << endl;
		return 1;
	}
	long bodysize = n;
	vector<Literal> body;

	if (readBody (f, bodysize, true, body)){
		return 1;
	}

	genrules.push_back(GenRule(atleast, heads, body));

	return 0;
}

int Read::addChoiceRule (istream &f){
	long n;

	// Heads
	f >> n;
	if (!f.good () || n < 1){
		cerr << "head size less than one, line " << linenumber << endl;
		return 1;
	}
	long headssize = n;

	vector<Literal> heads;
	for (long i = 0; i < headssize; i++){
		f >> n;
		if (!f.good () || n < 1){
			cerr << "atom out of bounds, line " << linenumber << endl;
			return 1;
		}
		heads.push_back(makeLiteral(n));
	}

	// Body
	f >> n;
	if (!f.good () || n < 0){
		cerr << "total body size, line " << linenumber << endl;
		return 1;
	}
	long bodysize = n;
	vector<Literal> body;

	// Negative body size
	f >> n;
	if (!f.good () || n < 0 || n > bodysize){
		cerr << "negative body size, line " << linenumber << endl;
		return 1;
	}
	long negbodysize = n;

	// Negative body
	if (readBody (f, negbodysize, false, body)){
		return 1;
	}
	// Positive body
	if (readBody (f, bodysize-negbodysize, true, body)){
		return 1;
	}

	choicerules.push_back(ChoiceRule(heads, body));

	return 0;
}

int Read::addWeightRule (istream &f){
	long n;

	// Rule head
	f >> n;
	if (!f.good () || n < 1){
		cerr << "head atom out of bounds, line " << linenumber << endl;
		return 1;
	}
	Atom head(n);

	Weight lowerbound;

	// Atleast
	f >> lowerbound;
	if (!f.good ()){
		return 1;
	}

	// Body
	f >> n;
	if (!f.good () || n < 0){
		cerr << "total body size, line " << linenumber << endl;
		return 1;
	}
	long bodysize = n;
	vector<Literal> body;

	// Negative body size
	f >> n;
	if (!f.good () || n < 0 || n > bodysize){
		cerr << "negative body size, line " << linenumber << endl;
		return 1;
	}
	long negbodysize = n;

	// Negative body
	if (readBody (f, negbodysize, false, body)){
		return 1;
	}
	// Positive body
	if (readBody (f, bodysize-negbodysize, true, body)){
		return 1;
	}

	vector<Weight> weights;
	Weight sum = 0, w = 0;
	for (long i = 0; i < bodysize; i++){
		f >> w;
		if (!f.good ()){
			return 1;
		}
		if (sum+w < sum){
			cerr << "sum of weights in weight rule too large,"
					<< " line " << linenumber << endl;
			return 1;
		}
		sum += w;
		weights.push_back(w);
	}

	if(!getSolver()->addSet(setcount, body, weights)){
		return 1;
	}
	if(!getSolver()->addAggrExpr(head, setcount, lowerbound, false, SUM, true)){
		return 1;
	}
	setcount++;

	return 0;
}

int Read::addOptimizeRule (istream &f){
	throw idpexception("Not yet implemented.");
 /* long n;
  api->begin_rule (OPTIMIZERULE);
  // Optimize
  f >> n;
  if (!f.good ())
    return 1;
  if (n)
    {
      cerr << "maximize statements are no longer accepted, line"
	   << linenumber << endl;
      return 1;
    }
  // Body
  f >> n;
  if (!f.good () || n < 0)
    return 1;
  long body = n;
  // Negative body
  f >> n;
  if (!f.good () || n < 0 || n > body)
    return 1;
  long nbody = n;
  if (readBody (f, nbody, false))
    return 1;
  // Positive body
  if (readBody (f, body-nbody, true))
    return 1;
  Weight w;
# ifdef USEDOUBLE
  f.precision (DBL_DIG);
# endif
  Weight sum = 0;
  for (long i = 0; i < body; i++)
    {
      f >> w;
      if (!f.good ())
	return 1;
      if (sum+w < sum)
	{
	  cerr << "sum of weights in optimize statement too large,"
	       << " line " << linenumber << endl;
	  return 1;
	}
      sum += w;
      if (i < nbody)
	api->change_body (i, false, w);
      else
	api->change_body (i-nbody, true, w);
    }
  api->end_rule ();*/
  return 0;
}

int Read::finishGenerateRules(){
	for(vector<GenRule>::const_iterator i=genrules.begin(); i<genrules.end(); i++){
		if((*i).body.size()!=0){
			for(vector<Literal>::const_iterator j=(*i).heads.begin(); j<(*i).heads.end(); j++){
				//TODO if an element is defined in multiple gen/choice rules, i think this will fail
				int atemp = maxatomnumber++;
				vector<Literal> tempbody((*i).body);
				tempbody.push_back(makeLiteral(atemp, true));
				if(!getSolver()->addRule(true, *j, tempbody)){
					return 1;
				}
				tempbody.clear();
				tempbody.push_back(Literal((*j).getAtom(), true));
				if(!getSolver()->addRule(true, makeLiteral(atemp), tempbody)){
					return 1;
				}
			}
		}

		if(!getSolver()->addSet(setcount, (*i).heads)){
			return 1;
		}
		int atemp = maxatomnumber++;
		if(!getSolver()->addAggrExpr(Literal(atemp), setcount, (*i).atleast, false, CARD, true)){
			return 1;
		}
		if(!getSolver()->addRule(true, Literal(atemp), (*i).body)){
			return 1;
		}
		setcount++;
	}

	return 0;

}

int Read::finishChoiceRules(){
	for(int i=0; i<choicerules.size(); i++){
		if(choicerules[i].body.size()==0){
			continue;
		}
		for(vector<Literal>::const_iterator j=choicerules[i].heads.begin(); j<choicerules[i].heads.end(); j++){
			int atemp = maxatomnumber++;
			vector<Literal> tempbody(choicerules[i].body);
			tempbody.push_back(makeLiteral(atemp, true));
			if(!getSolver()->addRule(true, *j, tempbody)){
				return 1;
			}
			tempbody.clear();
			tempbody.push_back(Literal((*j).getAtom(), true));
			if(!getSolver()->addRule(true, makeLiteral(atemp), tempbody)){
				return 1;
			}
		}
	}
	return 0;
}

int Read::read (istream &f){
	// Read rules.
	int type;
	bool stop = false;
	for (linenumber = 1; !stop; linenumber++){
		// Rule Type
		f >> type;
		switch (type){
			case ENDRULE:
				stop = true;
				break;
			case BASICRULE:
				if (addBasicRule (f)){
					return 1;
				}
				break;
			case CONSTRAINTRULE:
				if (addConstraintRule (f)){
					return 1;
				}
				break;
			case CHOICERULE:
				if (addChoiceRule (f)){
					return 1;
				}
				break;
			case GENERATERULE:
				if (addGenerateRule (f)){
					return 1;
				}
				break;
			case WEIGHTRULE:
				if (addWeightRule (f)){
					return 1;
				}
				break;
			case OPTIMIZERULE:
				if (addOptimizeRule (f)){
					return 1;
				}
				break;
			default:
				return 1;
		}
	}
	// Read atom names (are currently completely ignored)
	const int len = 1024;
	char s[len];
	long i;
	f.getline (s, len);  // Get newline
	if (!f.good ()){
		cerr << "expected atom names to begin on new line, line "
		<< linenumber << endl;
		return 1;
	}
	f >> i;
	f.getline (s, len);
	linenumber++;
	while (i){
		if (!f.good ())	{
			cerr << "atom name too long or end of file, line "
					<< linenumber << endl;
			return 1;
		}
//		Atom *a = getAtom (i);
//		if (*s){
//			api->set_name (a, s+1);
//		}else{
//			api->set_name (a, 0);
//		}
		f >> i;
		f.getline (s, len);
		linenumber++;
	}

	// Read compute-statement
	f.getline (s, len);
	if (!f.good () || strcmp (s, "B+")){
		cerr << "B+ expected, line " << linenumber << endl;
		return 1;
	}
	linenumber++;
	f >> i;
	linenumber++;
	while (i){
		if (!f.good () || i < 1){
			cerr << "B+ atom out of bounds, line " << linenumber << endl;
			return 1;
		}

		vector<Literal> lits;
		lits.push_back(makeLiteral(i));
		if(!getSolver()->addClause(lits)){
			return 1;
		}

		f >> i;
		linenumber++;
	}
	f.getline (s, len);  // Get newline.
	f.getline (s, len);
	if (!f.good () || strcmp (s, "B-")){
		cerr << "B- expected, line " << linenumber << endl;
		return 1;
	}
	linenumber++;
	f >> i;
	linenumber++;
	while (i){
		if (!f.good () || i < 1){
			cerr << "B- atom out of bounds, line " << linenumber << endl;
			return 1;
		}

		vector<Literal> lits;
		lits.push_back(makeLiteral(i, true));
		if(!getSolver()->addClause(lits)){
			return 1;
		}

		f >> i;
		linenumber++;
	}

	f >> i;  // zero means all
	getSolver()->setNbModels(i);

	if (f.fail ()){
		cerr << "number of models expected, line " << linenumber << endl;
		return 1;
	}

	if(finishChoiceRules()==1){
		return 1;
	}
	if(finishGenerateRules()==1){
		return 1;
	}

	return 0;
}
