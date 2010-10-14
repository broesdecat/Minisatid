#include <vector>
#include <fstream>
#include "pbsolver/pbbase/h/GenralBaseFunctions.h"

using namespace PBSolver;

using namespace std;
#define length(a) ( sizeof ( a ) / sizeof ( *a ) )

unsigned long long PBSolver::inputCountEval(unsigned int ws[][2], vector<int> &base,int wsLength) {
	return inputCountEval(base,0,ws,1,0,wsLength);
}
unsigned long long PBSolver::compCountEval(unsigned int ws[][2], vector<int> &base,int wsLength) {
	return compCountEval(base,0,ws,1,0,wsLength);
}

unsigned long long PBSolver::carryOnlyEval(unsigned int ws[][2], vector<int> &base,int wsLength){
	return carryOnlyEval(base,0,ws,1,0,wsLength);
}

unsigned long long PBSolver::sumOfDigitsEval(unsigned int ws[][2], vector<int> &base,int wsLength){
	return sumOfDigitsEval(base,0,ws,1,wsLength);
}



void PBSolver::carryVecEval(unsigned int ws[][2], vector<int> &base,int wsLength,vector<unsigned long long> &carry){
	carry.clear();
	carryVecEval(base,0,ws,1,0,wsLength,carry);
}

void PBSolver::carryVecEval(vector<int> &base,unsigned int i, unsigned int ws[][2],unsigned long mul,unsigned long long ca,int lr,vector<unsigned long long> &carry){
	if (lr==0 || i==base.size())
		return;
	else {
	     unsigned int p = base[i];
 	     unsigned long long rest = ca;   // Sum of all the remainders.
	     unsigned long long div;
	     unsigned int nlr=0;
	     for (int j = 0; j < lr; j++){
	    	 unsigned long temp = ws[j][0] / mul;
	         rest +=  (temp % p) * ws[j][1];
	         div = temp /p;
	         if (div > 0)
	             nlr++;
	     }
	     carry.push_back(rest/p);
	     carryVecEval(base,i+1,ws,mul*p,rest/p,nlr,carry);
	}
}


void PBSolver::inputVecEval(unsigned int ws[][2], vector<int> &base,int wsLength,vector<unsigned long long> &input){
	input.clear();
	inputVecEval(base,0,ws,1,0,wsLength,input);
}

void PBSolver::inputVecEval(vector<int> &base,unsigned int i, unsigned int ws[][2],unsigned long mul,unsigned long long ca,int lr,vector<unsigned long long> &input){
	if (lr==0)
		return;
	else if (i==base.size()){
		unsigned long long temp=ca;
		for (int j = 0; j < lr; j++) 
			temp += (ws[j][0] / mul)*ws[j][1];
		input.push_back(temp);
	}
	else {
	     unsigned int p = base[i];
 	     unsigned long long rest = ca;   // Sum of all the remainders.
	     unsigned long long div;
	     unsigned int nlr=0;
	     for (int j = 0; j < lr; j++){
	    	 unsigned long temp = ws[j][0] / mul;
	         rest +=  (temp % p) * ws[j][1];
	         div = temp /p;
	         if (div > 0)
	             nlr++;
	     }
	     input.push_back(rest);
	     inputVecEval(base,i+1,ws,mul*p,rest/p,nlr,input);
	}
}

unsigned long long PBSolver::sumOfDigitsEval(vector<int> &base,unsigned int i, unsigned int ws[][2],unsigned long mul,int lr) {
	if (lr==0) 
		return 0;
	else if (i==base.size()){
		unsigned long long temp=0;
		for (int j = 0; j < lr; j++) 
			temp += (ws[j][0] / mul)*ws[j][1];
		return temp;
	}
	else {
	     unsigned int p = base[i];
 	     unsigned long long rest=0;   // Sum of all the remainders.
	     unsigned long long div;
	     unsigned int nlr=0;
	     for (int j = 0; j < lr; j++){
	    	 unsigned long temp = ws[j][0] / mul;
	         rest +=  (temp % p) * ws[j][1];
	         div = temp /p;
	         if (div > 0)
	             nlr++;
	     }
	     return rest+sumOfDigitsEval(base,i+1,ws,mul*p,nlr);
	}
}

unsigned long long PBSolver::carryOnlyEval(vector<int> &base,unsigned int i, unsigned int ws[][2],unsigned long mul,unsigned long long ca,int lr) {
	if (lr==0) 
		return 0;
	else if (i==base.size())
		return ca;
	else {
	     unsigned int p = base[i];
 	     unsigned long long rest = ca;   // Sum of all the remainders.
	     unsigned long long div;
	     unsigned int nlr=0;
	     for (int j = 0; j < lr; j++){
	    	 unsigned long temp = ws[j][0] / mul;
	         rest +=  (temp % p) * ws[j][1];
	         div = temp /p;
	         if (div > 0)
	             nlr++;
	     }
	     return ca+carryOnlyEval(base,i+1,ws,mul*p,rest/p,nlr);
	}
}

unsigned long long PBSolver::inputCountEval(vector<int> &base,unsigned int i, unsigned int ws[][2],unsigned long mul,unsigned long long ca,int lr) {
	if (lr==0) 
		return 0;
	else if (i==base.size()){
		unsigned long long temp=ca;
		for (int j = 0; j < lr; j++) 
			temp += (ws[j][0] / mul)*ws[j][1];
		return temp;
	}
	else {
	     unsigned int p = base[i];
 	     unsigned long long rest = ca;   // Sum of all the remainders.
	     unsigned long long div;
	     unsigned int nlr=0;
	     for (int j = 0; j < lr; j++){
	    	 unsigned long temp = ws[j][0] / mul;
	         rest +=  (temp % p) * ws[j][1];
	         div = temp /p;
	         if (div > 0)
	             nlr++;
	     }
	     return rest+inputCountEval(base,i+1,ws,mul*p,rest/p,nlr);
	}
}


unsigned long long PBSolver::compCountEval(vector<int> &base,unsigned int i, unsigned int ws[][2],unsigned long mul,unsigned long long ca,int lr) {
	if (lr==0) 
		return 0;
	else if (i==base.size()){
		unsigned long long temp=ca;
		for (int j = 0; j < lr; j++) 
			temp += (ws[j][0] / mul)*ws[j][1];
		return nlg2n2(temp);
	}
	else {
	     unsigned int p = base[i];
 	     unsigned long long rest = ca;   // Sum of all the remainders.
	     unsigned long long div;
	     unsigned int nlr=0;
	     for (int j = 0; j < lr; j++){
	    	 unsigned long long temp = ws[j][0] / mul;
	         rest +=  (temp % p) * ws[j][1];
	         div = temp /p;
	         if (div > 0)
	             nlr++;
	     }
	     return nlg2n2(rest)+compCountEval(base,i+1,ws,mul*p,rest/p,nlr);
	}
}

unsigned int PBSolver::loadPrimes(char* primes_file_name,std::vector<unsigned int>& pri,unsigned int maxW,unsigned int cutOF) {
	std::fstream file(primes_file_name, std::fstream::in);
	unsigned int p;
	unsigned int max = 15485863;
	if (maxW<max) max = maxW;
	if (cutOF<max) max = cutOF;
	while(true) { 
		file >> p;
		if(p>max) break;
		pri.push_back(p);
	}
	file.close();
	if    (cutOF>15485863) return 15485863;
	else  return cutOF;
}
