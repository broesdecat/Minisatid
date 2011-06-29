#include <vector>
#include <fstream>
#include <iostream>
#include "../h/GenralBaseFunctions.h"



namespace MiniSatPP {
	
#define length(a) ( sizeof ( a ) / sizeof ( *a ) )

uint64 inputCountEval(unsigned int ws[][2], std::vector<int> &base,int wsLength) {
	return inputCountEval(base,0,ws,1,0,wsLength);
}
uint64 compCountEval(unsigned int ws[][2], std::vector<int> &base,int wsLength) {
	return compCountEval(base,0,ws,1,0,wsLength);
}

uint64 oddEvenCountEval(unsigned int ws[][2], std::vector<int> &base,int wsLength) {
	return oddEvenCountEval(base,0,ws,1,0,wsLength);
}

uint64 carryOnlyEval(unsigned int ws[][2], std::vector<int> &base,int wsLength){
	return carryOnlyEval(base,0,ws,1,0,wsLength);
}

uint64 sumOfDigitsEval(unsigned int ws[][2], std::vector<int> &base,int wsLength){
	return sumOfDigitsEval(base,0,ws,1,wsLength);
}



void carryVecEval(unsigned int ws[][2], std::vector<int> &base,int wsLength,std::vector<uint64> &carry){
	carry.clear();
	carryVecEval(base,0,ws,1,0,wsLength,carry);
}

void carryVecEval(std::vector<int> &base,unsigned int i, unsigned int ws[][2],unsigned long mul,uint64 ca,int lr,std::vector<uint64> &carry){
	if (lr==0 || i==base.size())
		return;
	else {
	     unsigned int p = base[i];
 	     uint64 rest = ca;   // Sum of all the remainders.
	     uint64 div;
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


void inputVecEval(unsigned int ws[][2], std::vector<int> &base,int wsLength,std::vector<uint64> &input){
	input.clear();
	inputVecEval(base,0,ws,1,0,wsLength,input);
}

void inputVecEval(std::vector<int> &base,unsigned int i, unsigned int ws[][2],unsigned long mul,uint64 ca,int lr,std::vector<uint64> &input){
	if (lr==0)
		return;
	else if (i==base.size()){
		uint64 temp=ca;
		for (int j = 0; j < lr; j++) 
			temp += (ws[j][0] / mul)*ws[j][1];
		input.push_back(temp);
	}
	else {
	     unsigned int p = base[i];
 	     uint64 rest = ca;   // Sum of all the remainders.
	     uint64 div;
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

uint64 sumOfDigitsEval(std::vector<int> &base,unsigned int i, unsigned int ws[][2],unsigned long mul,int lr) {
	if (lr==0) 
		return 0;
	else if (i==base.size()){
		uint64 temp=0;
		for (int j = 0; j < lr; j++) 
			temp += (ws[j][0] / mul)*ws[j][1];
		return temp;
	}
	else {
	     unsigned int p = base[i];
 	     uint64 rest=0;   // Sum of all the remainders.
	     uint64 div;
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

uint64 carryOnlyEval(std::vector<int> &base,unsigned int i, unsigned int ws[][2],unsigned long mul,uint64 ca,int lr) {
	if (lr==0) 
		return 0;
	else if (i==base.size())
		return ca;
	else {
	     unsigned int p = base[i];
 	     uint64 rest = ca;   // Sum of all the remainders.
	     uint64 div;
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

uint64 inputCountEval(std::vector<int> &base,unsigned int i, unsigned int ws[][2],unsigned long mul,uint64 ca,int lr) {
	if (lr==0) 
		return 0;
	else if (i==base.size()){
		uint64 temp=ca;
		for (int j = 0; j < lr; j++) 
			temp += (ws[j][0] / mul)*ws[j][1];
		return temp;
	}
	else {
	     unsigned int p = base[i];
 	     uint64 rest = ca;   // Sum of all the remainders.
	     uint64 div;
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


uint64 compCountEval(std::vector<int> &base,unsigned int i, unsigned int ws[][2],unsigned long mul,uint64 ca,int lr) {
	if (lr==0) 
		return 0;
	else if (i==base.size()){
		uint64 temp=ca;
		for (int j = 0; j < lr; j++) 
			temp += (ws[j][0] / mul)*ws[j][1];
		return nlg2n2(temp);
	}
	else {
	     unsigned int p = base[i];
 	     uint64 rest = ca;   // Sum of all the remainders.
	     uint64 div;
	     unsigned int nlr=0;
	     for (int j = 0; j < lr; j++){
	    	 uint64 temp = ws[j][0] / mul;
	         rest +=  (temp % p) * ws[j][1];
	         div = temp /p;
	         if (div > 0)
	             nlr++;
	     }
	     return nlg2n2(rest)+compCountEval(base,i+1,ws,mul*p,rest/p,nlr);
	}
}

uint64 oddEvenCountEval(std::vector<int> &base,unsigned int i, unsigned int ws[][2],unsigned long mul,uint64 ca,int lr) {
	if (lr==0) 
		return 0;
	else if (i==base.size()){
		uint64 temp=ca;
		for (int j = 0; j < lr; j++) 
			temp += (ws[j][0] / mul)*ws[j][1];
		return oddEvenCount(temp);
	}
	else {
	     unsigned int p = base[i];
 	     uint64 rest = ca;   // Sum of all the remainders.
	     uint64 div;
	     unsigned int nlr=0;
	     for (int j = 0; j < lr; j++){
	    	 uint64 temp = ws[j][0] / mul;
	         rest +=  (temp % p) * ws[j][1];
	         div = temp /p;
	         if (div > 0)
	             nlr++;
	     }
	     return oddEvenCount(rest)+oddEvenCountEval(base,i+1,ws,mul*p,rest/p,nlr);
	}
}



unsigned int loadPrimes(const char* primes_file_name,std::vector<unsigned int>& pri,unsigned int maxW,unsigned int cutOF) {
	std::fstream file(primes_file_name, std::fstream::in);
	if(file.fail()){
		std::cerr << "Error: File containing primes could not be read, aborting program!" <<std::endl;
		exit(1);
	}
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
}
