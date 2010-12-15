#include "Hardware.h"

namespace MiniSatPP {
	
//- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

/*macro Formula operator && (Formula f, Formula g)
{
    if      (f == _0_ || g == _0_) return _0_;
    else if (f == _1_)             return g;
    else if (g == _1_)             return f;
    else if (f ==  g )             return f;
    else if (f == ~g )             return _0_;

    if (g < f) swp(f, g);
    return Bin_new(op_And, f, g);
}

macro Formula operator || (Formula f, Formula g) {
    return ~(~f && ~g); }*/

//- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -


static inline void cmp2(vec<Formula>& fs, int begin) {
    Formula a     = fs[begin];
    Formula b     = fs[begin + 1];
//#if 1
    fs[begin]     = a | b;
    fs[begin + 1] = a & b;
/*#else
    fs[begin]     = a || b;
    fs[begin + 1] = a && b;
#endif*/
}

//@pre j>i
static inline void cmp2(vec<Formula>& fs, int i,int j) {
    Formula a     = fs[i];
    Formula b     = fs[j];
    fs[i] = a | b;
    fs[j] = a & b;
}

static void riffle(vec<Formula>& fs) {
    vec<Formula> tmp; fs.copyTo(tmp);
    for (int i = 0; i < fs.size() / 2; i++){
        fs[i*2]   = tmp[i];
        fs[i*2+1] = tmp[i+fs.size() / 2];
    }
}

static void unriffle(vec<Formula>& fs) {
    vec<Formula> tmp; fs.copyTo(tmp);
    for (int i = 0; i < fs.size() / 2; i++){
        fs[i]               = tmp[i*2];
        fs[i+fs.size() / 2] = tmp[i*2+1];
    }
}

static void oddEvenMerge(vec<Formula>& fs, int begin, int end) {
    assert(end - begin > 1);
    if (end - begin == 2)
        cmp2(fs,begin);
    else {
        int          mid = (end - begin) / 2;
        vec<Formula> tmp;
        for (int i = 0; i < end - begin; i++)
            tmp.push(fs[begin+i]);
        unriffle(tmp);
        oddEvenMerge(tmp,0,mid);
        oddEvenMerge(tmp,mid,tmp.size());
        riffle(tmp);
        for (int i = 1; i < tmp.size() - 1; i += 2)
            cmp2(tmp,i);
        for (int i = 0; i < tmp.size(); i++)
            fs[i + begin] = tmp[i];
    }
}

static void totlizerMerge(vec<Formula>& toMerge, int begin, int end) {
	assert(end - begin > 1);
	if (end - begin == 2)
        cmp2(toMerge,begin);
    else {
		vec<Formula> merged;
		merged.growTo(end-begin,_0_);
		int mid = (end-begin)/2;
		for(int i=0;i<mid;i++) merged[i] = toMerge[begin+i] | toMerge[begin+mid+i];
		for(int i=0;i<mid;i++) 
			for(int j=0;j<mid;j++) 
				merged[i+j+1] |= toMerge[begin+i] & toMerge[begin+mid+j];		
		for(int i=0;i<merged.size();i++) toMerge[begin+i] = merged[i];
    }
}

	static inline void split(vec<Formula>& toSplit,int n, int startPos) {
		for(int i1=startPos, i2=0; i2<n/2; i2++, i1++) {
			int j = i1 + n/2;
			cmp2(toSplit,i1,j);
		}
	}


	static inline void combine(vec<Formula>& toMerge,int n, int startPos, int m) {
		for(int i1=startPos + m, i2=1; i2 < n/2; i1+= 2*m, i2++) {
			int j = i1 + m;
			cmp2(toMerge,i1,j);
		}
	}

	/*
	 * n - the size of the merger input (output) size of the network
	 * startPos - the index of the first input wire within the complete merger network
	   m - the jump size: comparators would be set between the ith and (i+m)th wires.
	 */
	 static  void pw_merge(vec<Formula>& toMerge,int n, int startPos, int m) {
		if (n == 1) return;
		else {
			pw_merge(toMerge,n/2, startPos, 2*m);
			pw_merge(toMerge,n/2, startPos + m, 2*m);
			combine(toMerge,n, startPos, m);
		}
	}


	static  void pw_sort(vec<Formula>& toSort,int n,int startPos) {
			if (n == 1) return;
			else {
				split(toSort,n, startPos); 
				pw_sort(toSort,n/2, startPos);
				pw_sort(toSort,n/2, startPos+n/2);
				pw_merge(toSort,n, startPos, 1);
			}
	}
	
	
void pw_sort(vec<Formula>& fs) {
		int orig_sz = fs.size();
    	int sz; for (sz = 1; sz < fs.size(); sz *= 2);
    	fs.growTo(sz,_0_);
		pw_sort(fs,sz, 0);
		fs.shrink(sz - orig_sz);
}

static inline void add(vec<Formula>& Xs,vec<Formula>& Ys) {
	for (int i = 0; i < Xs.size(); i++) Ys.push(Xs[i]);
}

// Inputs to the circuit is the formulas in fs, which is overwritten
// by the resulting outputs of the circuit.
// NOTE: The number of comparisons is bounded by: n * log n * (log n + 1)
void oddEvenSort(vec<Formula>& fs) {
    int orig_sz = fs.size();
    int sz; for (sz = 1; sz < fs.size(); sz *= 2);
    fs.growTo(sz,_0_);

    for (int i = 1; i < fs.size(); i *= 2)
        for (int j = 0; j + 2*i <= fs.size(); j += 2*i)
            oddEvenMerge(fs,j,j+2*i);
    fs.shrink(sz - orig_sz);
}


static inline void  mergeNetwork(vec<Formula>& toMerge,int begin,int end,vec<Formula>& propgationShortCuts){
	if (end-begin<=8)
		totlizerMerge(toMerge, begin, end);
	else 	
		oddEvenMerge(toMerge, begin, end);
	for (int i=0;i<end-begin;i++) 
		propgationShortCuts[i] |= toMerge[i+begin];
}


static inline void  mergeNetwork(vec<Formula>& Xs,vec<Formula>& Ys,vec<Formula>& Merged,vec<Formula>& propgationShortCuts){
	int begin = Merged.size();
	add(Xs,Merged);
	add(Ys,Merged);
	mergeNetwork(Merged,begin, Merged.size(),propgationShortCuts);
}

static inline void sortNetwork(vec<Formula>& toSort,vec<Formula>& propgationShortCuts) {
	for (int i = 1; i < toSort.size(); i *= 2) 
        for (int j = 0; j + 2*i <= toSort.size(); j += 2*i) 
        	mergeNetwork(toSort,j,j+2*i,propgationShortCuts);
}

static inline void safeSortNetwork(vec<Formula>& toSort,vec<Formula>& propgationShortCuts) {
	int toSort_orig_sz = toSort.size();
	int psc_orig_sz = propgationShortCuts.size();
    int sz; for (sz = 1; sz < toSort.size(); sz *= 2);
    toSort.growTo(sz,_0_);
    propgationShortCuts.growTo(sz,_0_);
	sortNetwork(toSort,propgationShortCuts);
	toSort.shrink(sz - toSort_orig_sz);
	if (sz>psc_orig_sz) propgationShortCuts.shrink(sz - toSort_orig_sz);
}

static inline void splitToGroups(vec<Formula>& Xs,int subS,vec<vec<Formula> >& SubXs){
	for (int i=0;i<Xs.size();i++){
		if (i % subS==0) SubXs.push();
		SubXs.last().push(Xs[i]);
	}
	SubXs.last().growTo(subS,_0_);
}

static inline void sortGroups(vec<vec<Formula> >& SubXs,vec<Formula>& propgationShortCuts){
	//assumes first group is already sorted
	for (int i=1;i<SubXs.size();i++) sortNetwork(SubXs[i],propgationShortCuts);
}

static inline void mergeGroups(vec<vec<Formula> >& Groups,int GroupSize, vec<Formula>& merged,vec<Formula>& propgationShortCuts) {
	int ngs; for (ngs = 2; ngs < Groups.size(); ngs *= 2);
	for (int i = Groups.size();i< ngs;i++) {
		Groups.push();
		Groups.last().growTo(GroupSize,_0_);
	} 
	int totalSize = GroupSize*ngs;
	propgationShortCuts.growTo(totalSize,_0_);
	for (int i=0;i<ngs;i++) add(Groups[i],merged);
	for (int i = GroupSize; i < merged.size(); i *= 2) 
        for (int j = 0; j + 2*i <= merged.size(); j += 2*i)	
        	mergeNetwork(merged,j,j+2*i,propgationShortCuts);
}

static inline void overwrite(vec<Formula>& me,vec<Formula>& with){
	for(int i=0;i<me.size();i++) me[i]= with[i];
}
   
static inline void addShortCuts(vec<Formula>& from,vec<Formula>& to){
		    for (int j=0;j<from.size();j++) to[j] |= from[j];
}
	
void unarySortAdd(vec<Formula>& Xs,vec<Formula>& Ys,vec<Formula>& out_sorter,bool useShortCuts){
 	vec<Formula> propgationShortCuts;
	int XsLen = Xs.size();
    int YsLen = Ys.size();
    if (YsLen==0) {
    	if (XsLen>0) {
    		add(Xs,out_sorter);
    		safeSortNetwork(out_sorter,propgationShortCuts);
    		if (useShortCuts) overwrite(out_sorter,propgationShortCuts);
    	}
    }
    else if (XsLen==0) add(Ys,out_sorter);
    else if (XsLen==1 & YsLen==1) {
    	add(Xs,out_sorter);
    	add(Ys,out_sorter);
    	cmp2(out_sorter, 0);
    }
    else {
    	int Ysize; for (Ysize = 2; Ysize < YsLen; Ysize *= 2);
    	Ys.growTo(Ysize,_0_);
    	propgationShortCuts.growTo(Ysize*2,_0_);
    	addShortCuts(Ys,propgationShortCuts);
    	if (XsLen <= YsLen) {
		    Xs.growTo(Ysize,_0_);
		    sortNetwork(Xs,propgationShortCuts);
		    mergeNetwork(Xs,Ys,out_sorter,propgationShortCuts);
		}
		else {
		    vec<vec<Formula> > SubXs;
		    SubXs.push();
		    add(Ys,SubXs.last());
		    splitToGroups(Xs, Ysize, SubXs);
		    sortGroups(SubXs,propgationShortCuts); 
		    mergeGroups(SubXs, Ysize, out_sorter,propgationShortCuts);
		}
		out_sorter.shrink(out_sorter.size() - XsLen-YsLen);
		if(useShortCuts) overwrite(out_sorter,propgationShortCuts);
    }
}

}
