#ifndef GENRALBASEFUNCTIONS_H_
#define GENRALBASEFUNCTIONS_H_

#include <vector>
#include <cmath>

using namespace std;
namespace PBSolver{
unsigned long long sumOfDigitsEval(unsigned int ws[][2], vector<int> &base,int wsLength);
unsigned long long inputCountEval(unsigned int ws[][2], vector<int> &base,int wsLength);
unsigned long long compCountEval(unsigned int ws[][2], vector<int> &base,int wsLength);
unsigned long long carryOnlyEval(unsigned int ws[][2], vector<int> &base,int wsLength);

unsigned long long sumOfDigitsEval(vector<int> &base,unsigned int i, unsigned int ws[][2],unsigned long mul,int lr);
unsigned long long inputCountEval(vector<int> &base,unsigned int i, unsigned int ws[][2],unsigned long mul,unsigned long long ca,int lr);
unsigned long long compCountEval(vector<int> &base,unsigned int i, unsigned int ws[][2],unsigned long mul,unsigned long long ca,int lr);
unsigned long long carryOnlyEval(vector<int> &base,unsigned int i, unsigned int ws[][2],unsigned long mul,unsigned long long ca,int lr);


void carryVecEval(unsigned int ws[][2], vector<int> &base,int wsLength,vector<unsigned long long> &carry);
void carryVecEval(vector<int> &base,unsigned int i, unsigned int ws[][2],unsigned long mul,unsigned long long ca,int lr,vector<unsigned long long> &carry);

void inputVecEval(unsigned int ws[][2], vector<int> &base,int wsLength,vector<unsigned long long> &input);
void inputVecEval(vector<int> &base,unsigned int i, unsigned int ws[][2],unsigned long mul,unsigned long long ca,int lr,vector<unsigned long long> &input);

unsigned int loadPrimes(char* primes_file_name,std::vector<unsigned int>& pri,unsigned int maxW,unsigned int cutOF);



inline unsigned long long oddEvenCount(register unsigned long long v) {
	switch(v){
		case 0 : return 0;
		case 1 : return 1;
		case 2 : return 2;
		case 3 : return 3;
		case 4 : return 5;
		default:
            register unsigned long long lg = (unsigned long long)llrint(log2(v));
            if (lg==0) lg=1;
		    return v*((lg*lg-1) / 4); //T(n)=n(1-1/n + (lg(n) * lg(n) -1)/4 )
	}
	return v;
}


inline unsigned long long nlg2n2(register unsigned long long v) {
  register unsigned long long lg2 = (unsigned long long)(llrint(log2(v)));
  if (lg2==0) lg2=1;
  return lg2*lg2*v;
}



inline unsigned int lg2(register unsigned int v) {
	return (unsigned int)(lrint(log2(v)));
}

}
       
#endif /*GENRALBASEFUNCTIONS_H_*/
