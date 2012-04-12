#include <vector>


#include "../h/GenralBaseFunctions.h"



namespace MiniSatPP {
	
#define length(a) ( sizeof ( a ) / sizeof ( *a ) )

unsigned long long inputCountEval(unsigned int ws[][2], std::vector<int> &base,int wsLength) { 
	return inputCountEval(base,0,ws,1,0,wsLength);
}
unsigned long long compCountEval(unsigned int ws[][2], std::vector<int> &base,int wsLength) { 
	return compCountEval(base,0,ws,1,0,wsLength);
}

unsigned long long oddEvenCountEval(unsigned int ws[][2], std::vector<int> &base,int wsLength) { 
	return oddEvenCountEval(base,0,ws,1,0,wsLength);
}

unsigned long long carryOnlyEval(unsigned int ws[][2], std::vector<int> &base,int wsLength){
	return carryOnlyEval(base,0,ws,1,0,wsLength);
}

unsigned long long sumOfDigitsEval(unsigned int ws[][2], std::vector<int> &base,int wsLength){
	return sumOfDigitsEval(base,0,ws,1,wsLength);
}



void carryVecEval(unsigned int ws[][2], std::vector<int> &base,int wsLength,std::vector<unsigned long long> &carry){
	carry.clear();
	carryVecEval(base,0,ws,1,0,wsLength,carry);
}

void carryVecEval(std::vector<int> &base,unsigned int i, unsigned int ws[][2],unsigned long mul,unsigned long long ca,int lr,std::vector<unsigned long long> &carry){
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


void inputVecEval(unsigned int ws[][2], std::vector<int> &base,int wsLength,std::vector<unsigned long long> &input){
	input.clear();
	inputVecEval(base,0,ws,1,0,wsLength,input);
}

void inputVecEval(std::vector<int> &base,unsigned int i, unsigned int ws[][2],unsigned long mul,unsigned long long ca,int lr,std::vector<unsigned long long> &input){
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

unsigned long long sumOfDigitsEval(std::vector<int> &base,unsigned int i, unsigned int ws[][2],unsigned long mul,int lr) {
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

unsigned long long carryOnlyEval(std::vector<int> &base,unsigned int i, unsigned int ws[][2],unsigned long mul,unsigned long long ca,int lr) {
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

unsigned long long inputCountEval(std::vector<int> &base,unsigned int i, unsigned int ws[][2],unsigned long mul,unsigned long long ca,int lr) {
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


unsigned long long compCountEval(std::vector<int> &base,unsigned int i, unsigned int ws[][2],unsigned long mul,unsigned long long ca,int lr) {
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

unsigned long long oddEvenCountEval(std::vector<int> &base,unsigned int i, unsigned int ws[][2],unsigned long mul,unsigned long long ca,int lr) {
	if (lr==0) 
		return 0;
	else if (i==base.size()){
		unsigned long long temp=ca;
		for (int j = 0; j < lr; j++) 
			temp += (ws[j][0] / mul)*ws[j][1];
		return oddEvenCount(temp);
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
	     return oddEvenCount(rest)+oddEvenCountEval(base,i+1,ws,mul*p,rest/p,nlr);
	}
}


PrimesLoader::PrimesLoader(const char* primes_file_name) :
	primesFile(primes_file_name, std::fstream::in) {
		unsigned int temp[]  = { 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97 };
		for (int i=0;i< sizeof ( temp ) / sizeof ( *temp );i++) backUpPrimes.push_back(temp[i]); 
		if (primesFile.is_open()) {
			if (primesFile.eof()) {
				primesFile.close();    //file is empty
				lastRead = 0; //last inedx used from back up prime array
			}
			else 
				primesFile>>lastRead; //readFirstPrime 
		}
		primes.push_back(2);                           //load first prime to vector	
	};
	
PrimesLoader::~PrimesLoader(){if (primesFile.is_open()) primesFile.close(); }

/**
 * @return the new cutoff for the search = min(cutOF,maxPrimeAvilvabeToLoader) 
 */
unsigned int PrimesLoader::loadPrimes(unsigned int maxW,unsigned int cutOF) {
	unsigned int max = maxW < cutOF ? maxW : cutOF ;
	if (primes.back()<max) { //more primes neaded to be loaded
		if (primesFile.is_open() && lastRead<max) { 
			while (!primesFile.eof() & lastRead<max) {
				primesFile >> lastRead; 
				primes.push_back(lastRead);
			}
			if (primesFile.eof()) {
				primesFile.close();
				lastRead = 0;
			}
		}
		if (!primesFile.is_open() & lastRead<backUpPrimes.size() && backUpPrimes[lastRead]<max) {
			while(lastRead<backUpPrimes.size() && backUpPrimes[lastRead]<=max)  {
				if (primes.back() < backUpPrimes[lastRead]) primes.push_back(backUpPrimes[lastRead]);
				lastRead++;
			}
			if (lastRead==backUpPrimes.size()) backUpPrimes.clear();
		}
	}
	if    (cutOF>primes.back()) return primes.back();
	else  					    return cutOF;
}

std::vector<unsigned int>& PrimesLoader::primeVector() {return primes;}




}
