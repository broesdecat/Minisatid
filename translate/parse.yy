%{
#include <assert.h>
#include <vector>
#include <map>
#include <iostream>
using namespace std;

extern int yylex(void);
extern char * yytext;
void yyerror(char* msg);

int lineNo;
int charPos;

char* copy(const char* input) {
   char* rslt = (char*)malloc(strlen(input)+1);
   strcpy(rslt, input);
   return rslt;
}

namespace translation {
   struct Symbol {
      Symbol(char* n, vector<char*>& tps, int f, int t, bool ip) : name(n), types(vector<char*>(tps)), from(f), to(t), isPred(ip) {}
      char * name;
      vector<char*> types;
      int from;
      int to; // derivable from "from", the types + their domain sizes
      bool isPred; // true : predicate, false: function symbol
      // bool show
   };

   struct ltstr {
      bool operator()(const char* s1, const char* s2) const {
         return strcmp(s1, s2) < 0;
      }
   };

   struct Data {
      vector<int> trues;
      vector<int> arbitraries;
      vector< pair< pair<char*,int>, int> > trues_ids;
      vector< pair< pair<char*,int>, int> > arbitraries_ids;

      map<const char*, int, ltstr> domains; // maps a domain-name to an integer, pointing into domain_elements
      vector< vector<char*> > domain_elements;

      vector<Symbol> symbols;
   };

   Data data;
}

vector<char*> v_transl;
bool parsing_trues;
bool parsing_arbitraries;
vector<int> numbers;

void addDomain(const char* name) {
   const char * domainname = copy(name);
   translation::data.domains[domainname] = translation::data.domain_elements.size();
   translation::data.domain_elements.push_back(vector<char*>(v_transl));
   v_transl.clear();
}

void printTuple(const translation::Symbol & s, int i) {
   int tuple_nr = i - s.from;
   assert(! s.types.empty());
   
   vector<char*> v = vector<char*>(s.types.size());
   
   for (int a = s.types.size()-1; a >= 0; --a) {
      char* name = s.types[a];
      vector<char*> * domain = &translation::data.domain_elements[translation::data.domains[name]];
      int domain_el = tuple_nr % domain->size();
      v[a] = (*domain)[domain_el];
      tuple_nr = tuple_nr / domain->size();
   }
   
   cout << v[0];
   int until = v.size(); if (!s.isPred) until--;
   for (int arg = 1; arg < until; ++arg)
      cout << ',' << v[arg];
   if (!s.isPred)
      cout << "->" << v[v.size()-1];
   cout << "; ";
}

void printTrues() {
   bool trues_known=false;
   
 	for (int s=0; s<translation::data.symbols.size(); s++) {
      translation::Symbol* sb = &translation::data.symbols[s];
		bool has_trues=false;
		for (int a=sb->from; a<sb->to; a++) {
			// is a in the original trues list, or is variables[a].lit now true?
			bool contains=false; int trs=0;
			while (trs<translation::data.trues.size() && !contains)// if we're sure that "trues" is ordered, this can go more efficient.
				if (translation::data.trues[trs++] == a)
					contains = true;
			if (contains) {
				if (has_trues)
               cout << "; ";
            else {
					has_trues = true;
               if (! trues_known) {
                  trues_known = true;
                  cout << "The following partial interpretation is part of every model:" << "\n";
               }
					cout << sb->name << " = {";
				}
            printTuple(*sb,a);
			}
		}
      if (has_trues)
         cout << '}' << "\n";
	}
	cout << "\n";
}

void printArbitraries() {
   bool arbitraries_known=false;
   
 	for (int s=0; s<translation::data.symbols.size(); s++) {
      translation::Symbol* sb = &translation::data.symbols[s];
		bool has_arbitraries=false;
		for (int a=sb->from; a<sb->to; a++) {
			// is a in the original arbitraries list, or is variables[a].lit now true?
			bool contains=false; int trs=0;
			while (trs<translation::data.arbitraries.size() && !contains)// if we're sure that "arbitraries" is ordered, this can go more efficient.
				if (translation::data.arbitraries[trs++] == a)
					contains = true;
			if (contains) {
				if (has_arbitraries)
               cout << "; ";
            else {
					has_arbitraries = true;
               if (! arbitraries_known) {
                  arbitraries_known = true;
                  cout << "The following tuples can be arbitrarily chosen:" << "\n";
               }
					cout << sb->name << " = {";
				}
            printTuple(*sb,a);
			}
		}
      if (has_arbitraries)
         cout << '}' << "\n";
	}
	cout << "\n";
}

void printModel(vector<int>& v) {

	printTrues();
	printArbitraries();		
   
   if (v.empty()) return;
   int vptr = 0;
   for (vector<translation::Symbol>::iterator it = translation::data.symbols.begin();
         it != translation::data.symbols.end();
         ++it) {
      // Skip v and it till they match. (This assumes both are ordered!!)
      while (abs(v[vptr]) < it->from) vptr++;
      if (abs(v[vptr]) >= it->to) continue;

      // print the symbol
      if (it->types.empty()) {
         cout << it->name << " = " << (v[vptr]>0 ? "true" : "false") << "\n";
         continue;
      }
      cout << it->name << " = ";
      if (it->isPred || it->types.size() != 1) cout << "{";

      // print the tuples
      while (vptr < v.size() && abs(v[vptr]) < it->to) {
         if (v[vptr] > 0)
            printTuple(*it, abs(v[vptr]));
         vptr++;
      }

      if (it->isPred || it->types.size() != 1) cout << "}";
      cout << "\n";
   }
   
}

%}

%union {
	int integer;
   char* character;
}

%token             ZERO TYPE PRED FUNC SHOW ISTRUE ARBITRARY COLON NEWLINE SLASH 
%token <integer>   NUMBER
%token <character> IDENTIFIER

%start transl

%%

transl   :  types symbols trues arbitraries
         ;

types    :  /* empty */
         |  types TYPE IDENTIFIER COLON dom_els NEWLINE              { addDomain($3); }
         ;

dom_els  :  /* empty */
         |  dom_els IDENTIFIER                                       { v_transl.push_back(copy($2)); }
         |  dom_els NUMBER                                           { char s[13]; sprintf(s,"%d",$2); v_transl.push_back(copy(s)); }
         ;
         
symbols  :  /* empty */
         |  symbols SHOW PRED NUMBER IDENTIFIER COLON args NEWLINE
            {  int add = 1;
               for (int a=0; a<v_transl.size(); ++a) // order <types> <symbols> has to be correct in order to do this!!
                  add *= translation::data.domain_elements[translation::data.domains[v_transl[a]]].size();
               translation::data.symbols.push_back(translation::Symbol(copy($5),v_transl,$4,$4+add,true));
               v_transl.clear();
            }
         |  symbols PRED NUMBER IDENTIFIER COLON args NEWLINE
            {  v_transl.clear();
            }
         |  symbols SHOW FUNC NUMBER IDENTIFIER COLON args NEWLINE
            {  int add = 1;
               for (int a=0; a<v_transl.size(); ++a) // order <types> <symbols> has to be correct in order to do this!!
                  add *= translation::data.domain_elements[translation::data.domains[v_transl[a]]].size();
               translation::data.symbols.push_back(translation::Symbol(copy($5),v_transl,$4,$4+add,false));
               v_transl.clear();
            }
         |  symbols FUNC NUMBER IDENTIFIER COLON args NEWLINE
            {  v_transl.clear();
            }
         ;

args     :  /* empty */
         |  args IDENTIFIER
            {  v_transl.push_back(copy($2));
            }
         ;
         
trues    :  ISTRUE COLON { parsing_trues = true; } lists NEWLINE
         ;

arbitraries : ARBITRARY COLON { parsing_trues = false; parsing_arbitraries = true; } lists NEWLINE whitespace
            ;

lists		:	/* empty */
			|	lists IDENTIFIER SLASH NUMBER numbers  /* predicate */
				{	if (parsing_trues) { // TODO (both here and under "function") take into account predicates and function symbols with same name!!
                  translation::data.trues_ids.push_back(pair<pair<char*,int>, int>(pair<char*,int>(copy($2), $4),translation::data.trues.size()));
                  for (int i=0; i<numbers.size(); i++)
                     translation::data.trues.push_back(numbers[i]);
                  numbers.clear();
               } else {
                  assert(parsing_arbitraries);
                  translation::data.arbitraries_ids.push_back(pair<pair<char*,int>, int>(pair<char*,int>(copy($2), $4),translation::data.arbitraries.size()));
                  for (int i=0; i<numbers.size(); i++)
                     translation::data.arbitraries.push_back(numbers[i]);
                  numbers.clear();
               }
				}
			|	lists IDENTIFIER SLASH NUMBER COLON numbers /* fuction */
				{	if (parsing_trues) {
                  translation::data.trues_ids.push_back(pair<pair<char*,int>, int>(pair<char*,int>(copy($2), $4),translation::data.trues.size()));
                  for (int i=0; i<numbers.size(); i++)
                     translation::data.trues.push_back(numbers[i]);
                  numbers.clear();
               } else {
                  assert(parsing_arbitraries);
                  translation::data.arbitraries_ids.push_back(pair<pair<char*,int>, int>(pair<char*,int>(copy($2), $4),translation::data.arbitraries.size()));
                  for (int i=0; i<numbers.size(); i++)
                     translation::data.arbitraries.push_back(numbers[i]);
                  numbers.clear();
               }
				}
			;
			
numbers  :  /* empty */
         |  numbers NUMBER
            {  numbers.push_back($2);
            }
         ;

whitespace  : /* empty */
            | whitespace NEWLINE
            ;
            
%%

/* yywrap: Called when EOF is reached on current input.
 * Have it return 1 if processing is finished, or
 * do something to fix the EOF condition (like open
 * another file and point to it) and return 0 to indicate
 * more input is available.
 */
//extern int yylex();

int yywrap() {
   cerr << "End of file reached before it was expected... bailing out." << "\n";
	return 1;
}
void yyerror(char* msg) {
   cerr << "Parse error: " << msg << "\n";
   exit(3);
}
