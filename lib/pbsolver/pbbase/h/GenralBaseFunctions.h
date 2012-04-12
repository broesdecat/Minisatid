#ifndef GENRALBASEFUNCTIONS_H_
#define GENRALBASEFUNCTIONS_H_

#include <vector>
#include <cmath>
#include <fstream>



namespace MiniSatPP {
	
static unsigned long long oddEvenCostF[] = {0,0,1,3,5,9,12,16,19,28,32,38,42,48,53,59,63,85,90,98,103,112,119,127,132,140,147,156,162,171,178,186,191,246,252,262,268,280,289,299,305,317,327,339,347,359,368,378,384,394,403,415,423,436,446,457,464,476,486,498,506,518,527,537,543,679,686,698,705,720,731,743,750,766,779,794,804,819,830,842,849,864,877,893,904,921,934,948,957,973,986,1001,1011,1026,1037,1049,1056,1068,1079,1094,1104,1121,1134,1148,1157,1174,1188,1204,1215,1231,1243,1256,1264,1279,1292,1308,1319,1336,1349,1363,1372,1388,1401,1416,1426,1441,1452,1464,1471,1800,1808,1822,1830,1848,1861,1875,1883,1903,1919,1937,1949,1967,1980,1994,2002,2022,2039,2059,2073,2094,2110,2127,2138,2158,2174,2192,2204,2222,2235,2249,2257,2275,2291,2311,2325,2347,2364,2382,2394,2416,2434,2454,2468,2488,2503,2519,2529,2549,2566,2586,2600,2621,2637,2654,2665,2685,2701,2719,2731,2749,2762,2776,2784,2798,2811,2829,2841,2862,2878,2895,2906,2928,2946,2966,2980,3000,3015,3031,3041,3062,3080,3101,3116,3138,3155,3173,3185,3206,3223,3242,3255,3274,3288,3303,3312,3330,3346,3366,3380,3402,3419,3437,3449,3471,3489,3509,3523,3543,3558,3574,3584,3604,3621,3641,3655,3676,3692,3709,3720,3740,3756,3774,3786,3804,3817,3831,3839,4617,4626,4642,4651,4672,4687,4703,4712,4736,4755,4776,4790,4811,4826,4842,4851,4876,4897,4921,4938,4963,4982,5002,5015,5039,5058,5079,5093,5114,5129,5145,5154,5178,5199,5224,5242,5269,5290,5312,5327,5354,5376,5400,5417,5441,5459,5478,5490,5515,5536,5560,5577,5602,5621,5641,5654,5678,5697,5718,5732,5753,5768,5784,5793,5814,5833,5857,5874,5901,5922,5944,5959,5987,6010,6035,6053,6078,6097,6117,6130,6157,6180,6206,6225,6252,6273,6295,6310,6336,6357,6380,6396,6419,6436,6454,6465,6489,6510,6535,6553,6580,6601,6623,6638,6665,6687,6711,6728,6752,6770,6789,6801,6826,6847,6871,6888,6913,6932,6952,6965,6989,7008,7029,7043,7064,7079,7095,7104,7120,7135,7156,7170,7195,7214,7234,7247,7274,7296,7320,7337,7361,7379,7398,7410,7437,7460,7486,7505,7532,7553,7575,7590,7616,7637,7660,7676,7699,7716,7734,7745,7770,7792,7818,7837,7865,7887,7910,7926,7954,7977,8002,8020,8045,8064,8084,8097,8123,8145,8170,8188,8214,8234,8255,8269,8294,8314,8336,8351,8373,8389,8406,8416,8437,8456,8480,8497,8524,8545,8567,8582,8610,8633,8658,8676,8701,8720,8740,8753,8780,8803,8829,8848,8875,8896,8918,8933,8959,8980,9003,9019,9042,9059,9077,9088,9112,9133,9158,9176,9203,9224,9246,9261,9288,9310,9334,9351,9375,9393,9412,9424,9449,9470,9494,9511,9536,9555,9575,9588,9612,9631,9652,9666,9687,9702,9718,9727};


unsigned long long sumOfDigitsEval(unsigned int ws[][2], std::vector<int> &base,int wsLength);
unsigned long long inputCountEval(unsigned int ws[][2], std::vector<int> &base,int wsLength);
unsigned long long compCountEval(unsigned int ws[][2], std::vector<int> &base,int wsLength);
unsigned long long oddEvenCountEval(unsigned int ws[][2], std::vector<int> &base,int wsLength);
unsigned long long carryOnlyEval(unsigned int ws[][2], std::vector<int> &base,int wsLength);

unsigned long long sumOfDigitsEval(std::vector<int> &base,unsigned int i, unsigned int ws[][2],unsigned long mul,int lr);
unsigned long long inputCountEval(std::vector<int> &base,unsigned int i, unsigned int ws[][2],unsigned long mul,unsigned long long ca,int lr);
unsigned long long compCountEval(std::vector<int> &base,unsigned int i, unsigned int ws[][2],unsigned long mul,unsigned long long ca,int lr);
unsigned long long oddEvenCountEval(std::vector<int> &base,unsigned int i, unsigned int ws[][2],unsigned long mul,unsigned long long ca,int lr);
unsigned long long carryOnlyEval(std::vector<int> &base,unsigned int i, unsigned int ws[][2],unsigned long mul,unsigned long long ca,int lr);


void carryVecEval(unsigned int ws[][2], std::vector<int> &base,int wsLength,std::vector<unsigned long long> &carry);
void carryVecEval(std::vector<int> &base,unsigned int i, unsigned int ws[][2],unsigned long mul,unsigned long long ca,int lr,std::vector<unsigned long long> &carry);

void inputVecEval(unsigned int ws[][2], std::vector<int> &base,int wsLength,std::vector<unsigned long long> &input);
void inputVecEval(std::vector<int> &base,unsigned int i, unsigned int ws[][2],unsigned long mul,unsigned long long ca,int lr,std::vector<unsigned long long> &input);


class PrimesLoader {
	
 public:
	PrimesLoader(const char* primes_file_name);
	virtual ~PrimesLoader();
	unsigned int loadPrimes(unsigned int maxW,unsigned int cutOF);
	std::vector<unsigned int>& primeVector();

 private:
    std::vector<unsigned int> backUpPrimes;
    std::vector<unsigned int> primes;
	std::fstream primesFile;
	unsigned int lastRead;
	 
};  


inline unsigned int lg2(register unsigned int v) {
	return (unsigned int)(lrint(log2(v)));
}

inline unsigned long long nlg2n2(register unsigned long long v) {
  register unsigned long long lg2 = (unsigned long long)(llrint(log2(v)));
  if (lg2==0) lg2=1;
  return lg2*lg2*v;
}


inline unsigned long long oddEvenCount(register unsigned long long v) {
				 if (v<=512) return oddEvenCostF[v];
				 else        return nlg2n2(v);
}




}   
#endif /*GENRALBASEFUNCTIONS_H_*/
