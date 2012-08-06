#include "PbSolver.h"
#include "Hardware.h"
#include "ADTs/Sort.h"
#include "pbbase/h/SearchMetaData.h"
#include "pbbase/h/GenralBaseFunctions.h"
#include "pbbase/h/BNB_SOD_Carry_Cost.h"
#include "pbbase/h/BNB_Comp_Cost.h"
#include "pbbase/h/BNB_oddEven_Cost.h"
#include "pbbase/h/ForwardSearch.h"
#include "pbbase/h/MiniSatOrig.h"
#include "pbbase/h/RelativeBaseSearch.h"
#include <map>
#include <assert.h>
#include <vector>
#include <cstdarg>

namespace MiniSatPP {
	
#define length(a) ( sizeof ( a ) / sizeof ( *a ) ) 
#define reportS(data) printf("\n%s, Cost=%lld ,  BasesEvaluated= %ld ,  Runtime= %ld , InsertedToQueue = %ld , NodesExpanded= %ld, CutOff=%d\n",data->algType,data->cost,data->basesEvaluated,data->runTime,data->insertedToQue,data->nodesExpended,data->primesCutOf);


//=================================================================================================
 

static inline void  vecToMultiSet(vec<Int>& inCoeffs,std::map<unsigned int,unsigned int>& multiSet) {
	 for (int i = 0; i < inCoeffs.size(); ++i) {
       multiSet[( int)toint(inCoeffs[i])]++;
     }
}

/**
 * From data structures used when searching for an optimized base
 * back to original MiniSAT+ data structures.
 *
 * @param data  the base will be read from here
 * @param outputBase  the entries of the base will be added here
 */
static inline void metaDataToBase(SearchMetaData* data, vec<int>& outputBase) {
  std::vector<int> inputBase = data->base;
  int size = inputBase.size();
  for (int i = 0; i < size; ++i) {
    outputBase.push(inputBase[i]);
  }
}


static inline void coeffsToDescendingWeights(std::map<unsigned int,unsigned int>& multiSet, unsigned int weights[][2]) {                     
	std::map<unsigned int, unsigned int>::reverse_iterator  rit;
	int i = 0;
	for ( rit=multiSet.rbegin() ; rit != multiSet.rend(); rit++ ) {
		weights[i][0] = (*rit).first;
		weights[i][1] = (*rit).second;
		if(i>0) assert(weights[i-1][0]>weights[i][0]); //For debuging prpous only 
		i++;
	}
}

//=================================================================================================

#define lit2fml(p) id(var(var(p)),sign(p))


static
void buildSorter(vec<Formula>& ps, vec<int>& Cs, vec<Formula>& out_sorter, PBOptions* options)
{
    out_sorter.clear();
    for (int i = 0; i < ps.size(); i++)
        for (int j = 0; j < Cs[i]; j++)
            out_sorter.push(ps[i]);
    if (options->opt_sorting_network_encoding==pairwiseSortEncoding)
    	pw_sort(out_sorter);
    else
    	oddEvenSort(out_sorter); // (overwrites inputs)
}

static
void buildSorter(vec<Formula>& ps, vec<Int>& Cs, vec<Formula>& out_sorter, PBOptions* options)
{
    vec<int>    Cs_copy;
    for (int i = 0; i < Cs.size(); i++)
        Cs_copy.push(toint(Cs[i]));
    buildSorter(ps, Cs_copy, out_sorter, options);
}

static void buildSorter(vec<Formula>& ps, vec<int>& Cs, vec<Formula>& carry , vec<Formula>& out_sorter, PBOptions* options) {
	out_sorter.clear();
	vec<Formula> Xs;
    for (int i = 0; i < ps.size(); i++)
        for (int j = 0; j < Cs[i]; j++)
            Xs.push(ps[i]);
    unarySortAdd(Xs, carry, out_sorter,options->opt_use_shortCuts);
}

static void buildSorter(vec<Formula>& ps, vec<Int>& Cs, vec<Formula>& carry , vec<Formula>& out_sorter, PBOptions* options) {
	vec<int>    Cs_copy;
    for (int i = 0; i < Cs.size(); i++)
        Cs_copy.push(toint(Cs[i]));
   buildSorter(ps,Cs_copy, carry , out_sorter, options);
}


class Exception_TooBig {};

static
void buildConstraint(vec<Formula>& ps, vec<Int>& Cs, vec<Formula>& carry, vec<int>& base, int digit_no, vec<vec<Formula> >& out_digits, int max_cost, PBOptions* options)
{
    assert(ps.size() == Cs.size());

    if (FEnv::topSize() > max_cost) throw Exception_TooBig();
    /**
    pf("buildConstraint(");
    for (int i = 0; i < ps.size(); i++)
        pf("%d*%s ", Cs[i], (*debug_names)[index(ps[i])]);
    pf("+ %d carry)\n", carry.size());
    **/

    if (digit_no == base.size()){
    	out_digits.push();
        // Final digit, build sorter for rest:
        // -- add carry bits:
        if (options->opt_sorting_network_encoding == unarySortAddEncoding)
        	 buildSorter(ps, Cs, carry, out_digits.last(), options);
        else {
	        for (int i = 0; i < carry.size(); i++)
	            ps.push(carry[i]),
	            Cs.push(1);
	        buildSorter(ps, Cs, out_digits.last(), options);
        }
    }else{
        vec<Formula>    ps_rem;
        vec<int>        Cs_rem;
        vec<Formula>    ps_div;
        vec<Int>        Cs_div;

        // Split sum according to base:
        int B = base[digit_no];
        for (int i = 0; i < Cs.size(); i++){
            Int div = Cs[i] / Int(B);
            int rem = toint(Cs[i] % Int(B));
            if (div > 0){
                ps_div.push(ps[i]);
                Cs_div.push(div);
            }
            if (rem > 0){
                ps_rem.push(ps[i]);
                Cs_rem.push(rem);
            }
        }
        vec<Formula> result;
		if (options->opt_sorting_network_encoding == unarySortAddEncoding)
        	 buildSorter(ps_rem, Cs_rem, carry, result, options);
        else {
	        // Add carry bits:
	        for (int i = 0; i < carry.size(); i++)
	            ps_rem.push(carry[i]),
	            Cs_rem.push(1);
	
	        // Build sorting network:
	        buildSorter(ps_rem, Cs_rem, result, options);
        }
        
        // Get carry bits:
        carry.clear();
        for (int i = B-1; i < result.size(); i += B)
            carry.push(result[i]);

        out_digits.push();
        for (int i = 0; i < B-1; i++){
            Formula out = _0_;
            for (int j = 0; j < result.size(); j += B){
                int n = j+B-1;
                if (j + i < result.size())
                    out |= result[j + i] & ((n >= result.size()) ? _1_ : ~result[n]);
            }
            out_digits.last().push(out);
        }

        buildConstraint(ps_div, Cs_div, carry, base, digit_no+1, out_digits, max_cost, options); // <<== change to normal loop
    }
}

/*
Naming:
  - a 'base' is a vector of integers, stating how far you count at that position before you wrap to the next digit (generalize base).
  - A 'dig' is an integer representing a digit in a number of some base.
  - A 'digit' is a vector of formulas, where the number of 1:s represents a digit in a number of some base.
*/


static
void convert(Int num, vec<int>& base, vec<int>& out_digs)
{
    for (int i = 0; i < base.size(); i++){
        out_digs.push(toint(num % Int(base[i])));
        num /= Int(base[i]);
    }
    out_digs.push(toint(num));
}


// Compare number lexicographically to output digits from sorter networks.
// Formula is TRUE when 'sorter-digits >= num'.
//
static
Formula lexComp(int sz, vec<int>& num, vec<vec<Formula> >& digits)
{
    if (sz == 0)
        return _1_;
    else{
/*
        printf("num    :"); for (int i = 0; i < sz; i++) printf(" %d", num[i]); printf("\n");
        printf("#digits:"); for (int i = 0; i < sz; i++) printf(" %d", digits[i].size()); printf("\n");
*/
        sz--;
        vec<Formula>& digit = digits[sz];
        int           dig   = num[sz];

        Formula gt = (digit.size() > dig) ? digit[dig] : _0_;       // This digit is greater than the "dig" of 'num'.
        Formula ge = (dig == 0) ? _1_ :
                     (digit.size() > dig-1) ? digit[dig-1] : _0_;   // This digit is greater than or equal to the "dig" of 'num'.

        /**/if (sz == 0) return ge;
        return gt | (ge & lexComp(sz, num, digits));
    }
}
static
Formula lexComp(vec<int>& num, vec<vec<Formula> >& digits) {
    assert(num.size() == digits.size());
    return lexComp(num.size(), num, digits); }


static
Formula buildConstraint(vec<Formula>& ps, vec<Int>& Cs, vec<int>& base, Int lo, Int hi, int max_cost, PBOptions* options)
{
    vec<Formula> carry;
    vec<vec<Formula> > digits;
    buildConstraint(ps, Cs, carry, base, 0, digits, max_cost, options);
    if (FEnv::topSize() > max_cost) throw Exception_TooBig();

    vec<int> lo_digs;
    vec<int> hi_digs;
    if (lo != Int_MIN)
        convert(lo, base, lo_digs);
    if (hi != Int_MAX)
        convert(hi+1, base, hi_digs);   // (+1 because we will change '<= x' to '!(... >= x+1)'


    /*DEBUG
    pf("Networks:");
    for (int i = 0; i < digits.size(); i++)
        pf(" %d", digits[i].size());
    pf("\n");

    if (lo != Int_MIN){
        pf("lo=%d :", lo); for (int i = 0; i < lo_digs.size(); i++) pf(" %d", lo_digs[i]); pf("\n"); }
    if (hi != Int_MAX){
        pf("hi+1=%d :", hi+1); for (int i = 0; i < hi_digs.size(); i++) pf(" %d", hi_digs[i]); pf("\n"); }
    END*/

/*
Base:  (1)    8    24   480
       aaa bbbbbb ccc ddddddd
Num:    2    0     5     6
*/

    Formula ret = ((lo == Int_MIN) ? _1_ :  lexComp(lo_digs, digits))
                & ((hi == Int_MAX) ? _1_ : ~lexComp(hi_digs, digits));
    if (FEnv::topSize() > max_cost) throw Exception_TooBig();
    return ret;
}


/*
a7...a1   b
0001111   001111111  00111
  ^^         ^        ^

a5 | (a4 & (b7 | b6 & (c3)))

a4
~a5 -> b6
~a6 & ~b7 -> c3
...

>= 404
*/

// yay prototype
SearchMetaData* searchForBase(vec<Int>& inCoeffs, vec<int>& outputBase,PrimesLoader& pl, PBOptions* options);

// Will return '_undef_' if 'cost_limit' is exceeded.
//
Formula buildConstraint(const Linear& c,PrimesLoader& pl, PBOptions* options, int max_cost)
{
    vec<Formula>    ps;
    vec<Int>        Cs;

    for (int j = 0; j < c.size; j++)
        ps.push(lit2fml(c[j])),
        Cs.push(c(j));
	
    vec<int> base;
  
    SearchMetaData* data = searchForBase(Cs, base, pl, options);
    FEnv::push();
    if (options->opt_dump) { // don't spend time on building unneeded formulae
        return _undef_;
    }
    Int lo = c.lo;
    Int hi = c.hi;
	if (options->opt_tare & (lo == hi | lo == Int_MIN | hi == Int_MAX)) {
		Int toNormlize;
		Int toAdd;
		if (lo == Int_MIN) toNormlize = hi;
		else                 toNormlize = lo;
		Int temp = 1;
		int i;
		for(i=0;temp<toNormlize && i<base.size();i++) temp *= base[i];
		if (temp < toNormlize) {
			i=2;
			while (temp*i < toNormlize) i++;
			temp*=i;
		}
		else {
			i--;
			Int bmi;
			if (i==-1) bmi=1;
			else       bmi = temp / base[i];   
			while(temp-bmi>=toNormlize) temp-=bmi;
			assert(temp > toNormlize);
		}
		toAdd = temp-toNormlize;
		if (toAdd>0) {
			ps.push(_1_);
			Cs.push(toAdd);
			if (lo != Int_MIN) lo=lo+toAdd;
			if (hi != Int_MAX) hi=hi+toAdd;
		}
	}
    Formula ret;
    try {
    	if (options->opt_verbosity >= 1) {
	    	if (c.lo != Int_MIN) {
	    		printf("orignal   lo:%5d     \n", (int)toint(c.lo));
	    		printf("normlized lo:%5d     \n", (int)toint(lo));
	    	}
	    	if  (c.hi != Int_MAX) {
	    		printf("orignal   hi:%5d     \n", (int)toint(c.hi));
	    		printf("normlized hi:%5d     \n", (int)toint(hi));
	    	}
    	}
        ret = buildConstraint(ps, Cs, base, lo, hi, max_cost, options);
    }catch (Exception_TooBig){
        FEnv::pop();
        return _undef_;
    }
	
	if (data!=0) data->fEnvSize = FEnv::topSize();
	
    if (options->opt_verbosity >= 1){
        printf("FEnv.topSize:%5d     ", FEnv::topSize());
        printf("Base:"); for (int i = 0; i < base.size(); i++) printf(" %d", base[i]); printf("\n");
    }
    FEnv::keep();
    return ret;
}

static void dump(std::map<unsigned int,unsigned int>& multiSet, PBOptions* options) {
  unsigned int timesSeenAlready = options->baseInputsDumped[multiSet];
  if (timesSeenAlready == 0) {
    int lastIndex = multiSet.size() - 1;
    int curIndex = 0;
    for (std::map<unsigned int, unsigned int>::iterator iter = multiSet.begin();
         iter != multiSet.end();
         iter++ ) {
      unsigned int value = iter->first;
      unsigned int count = iter->second;
      for (unsigned int i = 0; i < count; ++i) {
        printf("%d", value);
        if (i == count-1 && curIndex == lastIndex) {
          printf(";\n");
          fflush(stdout);
        } else {
          printf(",");
        }
      }
      ++curIndex;
    }
  }
  options->baseInputsDumped[multiSet]++;
}

/**
 * Probably one of the more interesting functions.
 */
SearchMetaData* searchForBase(vec<Int>& inCoeffs, vec<int>& outputBase,PrimesLoader& pl, PBOptions* options) {
  std::map<unsigned int,unsigned int> multiSet;
  vecToMultiSet(inCoeffs,multiSet);
  unsigned int weights[multiSet.size()][2];
  coeffsToDescendingWeights(multiSet, weights);
  SearchMetaData* data = 0;
  unsigned int cutof = pl.loadPrimes(weights[0][0],options->opt_max_generator);
  std::vector<unsigned int>& pri = pl.primeVector();
  if      (options->opt_base == base_Forward) data = findBaseFWD(weights, multiSet.size(), pri,cutof);
  else if (options->opt_base == base_SOD)     data = bnb_SOD_Carry_Cost_search(weights, multiSet.size(),pri,cutof,false,true,true);
  else if (options->opt_base == base_Carry)   data = bnb_SOD_Carry_Cost_search(weights, multiSet.size(), pri,cutof,options->opt_non_prime,options->opt_abstract);
  else if (options->opt_base == base_Comp)    data = bnb_Comp_Cost_search(weights, multiSet.size(), pri,cutof,options->opt_non_prime,options->opt_abstract);
  else if (options->opt_base == base_oddEven)    data = bnb_oddEven_Cost_search(weights, multiSet.size(), pri,cutof,options->opt_non_prime,options->opt_abstract);
  else if (options->opt_base == base_Rel)     data = bnb_Relative_search(weights, multiSet.size() , pri,cutof,options->opt_non_prime,options->opt_abstract);
  else if (options->opt_base == base_Bin) {
  		data =  new SearchMetaData(lg2(weights[0][0]),cutof,weights[0][0],multiSet.size(),"BinaryBase");
  		data->finalize(0);
  }    
  else if (options->opt_base == base_M) {
  	vec<Int> dummy;
    int      cost;
  	data = optimizeBase(inCoeffs, dummy, cost, outputBase,weights,multiSet.size(), cutof);
  }
  else printf("Unknown option!"), exit(-1);  
  data->inputCountCost = inputCountEval(weights,data->base,multiSet.size());
  data->carryOnlyCost  = carryOnlyEval(weights,data->base,multiSet.size());
  data->compCost       = compCountEval(weights,data->base,multiSet.size());
  for (unsigned int j=0;j<multiSet.size();j++){  	
  	data->emptyBaseNOI += weights[j][0]*weights[j][1];
  	data->numOfCoffes  += weights[j][1];
  }
  carryVecEval(weights,data->base,multiSet.size(),data->carry);
  inputVecEval(weights,data->base,multiSet.size(),data->inputs);
  if (options->opt_verbosity >= 1) {
    data->print();
  	printf("Run time is in micro seconds!!!\n");
  }
  if (options->opt_base != base_M) metaDataToBase(data, outputBase);
  options->baseMetaData.push_back(data);
  return data;
}


}
