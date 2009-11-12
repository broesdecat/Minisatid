// (c) Maarten Marien, 2007.

#include <fstream>
#include <iostream>
#include <string>
#include <vector>
#include <stdlib.h>
using namespace std;

extern int yyparse();
extern FILE* yyin;

extern void printModel(vector<int>& v);

int main(int argc, char **argv) {
  
   ++argv, --argc;// skip over program name

   // Read the translation data.
   if (argc>0)
      yyin = fopen(argv[1], "r");
   else
      yyin = stdin;
   yyparse();
   fclose(yyin);
   

   ifstream fin(argv[0]);
   string s;
   fin >> s;
   if (s=="UNSAT") {
      cout << "Unsatisfiable.\n";
      exit(0);
   } else if (s!="SAT") {
      cerr << "PARSE ERROR! Unexpected input. (Expected ``SAT'' or ``UNSAT''.) Bailing out.\n";
      exit(3);
   }

   vector<int> v;
   while (fin >> s) {
      v.push_back(atoi(s.c_str()));
      if (atoi(s.c_str())==0) {
          printModel(v);
          v.clear();
      }
   }
   fin.close();

   return 0;
}
