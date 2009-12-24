/***********************************************************************************[SolverTypes.h]
MiniSat -- Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/


#ifndef SolverTypes_h
#define SolverTypes_h

#include <cassert>
#include <stdint.h>

#define theoryUNSAT 20
#define memOVERFLOW 33

//=================================================================================================
// Variables, literals, lifted booleans, clauses:


// NOTE! Variables are just integers. No abstraction here. They should be chosen from 0..N,
// so that they can be used as array indices.

typedef int Var;
#define var_Undef (-1)


class Lit {
    int     x;
 public:
    Lit() : x(2*var_Undef)                                              { }   // (lit_Undef)
    explicit Lit(Var var, bool sign = false) : x((var+var) + (int)sign) { }

    // Don't use these for constructing/deconstructing literals. Use the normal constructors instead.
    friend int  toInt       (Lit p);  // Guarantees small, positive integers suitable for array indexing.
    friend Lit  toLit       (int i);  // Inverse of 'toInt()'
    friend Lit  operator   ~(Lit p);
    friend bool sign        (Lit p);
    friend int  var         (Lit p);
    friend Lit  unsign      (Lit p);
    friend Lit  id          (Lit p, bool sgn);

    friend int  hash        (Lit p) { return toInt(p); }

    bool operator == (Lit p) const { return x == p.x; }
    bool operator != (Lit p) const { return x != p.x; }
    bool operator <  (Lit p) const { return x < p.x;  } // '<' guarantees that p, ~p are adjacent in the ordering.
};

inline  int  toInt       (Lit p)           { return p.x; }
inline  Lit  toLit       (int i)           { Lit p; p.x = i; return p; }
inline  Lit  operator   ~(Lit p)           { Lit q; q.x = p.x ^ 1; return q; }
inline  bool sign        (Lit p)           { return p.x & 1; }
inline  int  var         (Lit p)           { return p.x >> 1; }
inline  Lit  unsign      (Lit p)           { Lit q; q.x = p.x & ~1; return q; }
inline  Lit  id          (Lit p, bool sgn) { Lit q; q.x = p.x ^ (int)sgn; return q; }

const Lit lit_Undef(var_Undef, false);  // }- Useful special constants.
const Lit lit_Error(var_Undef, true );  // }


//=================================================================================================
// Lifted booleans:


class lbool {
    char     value;
    explicit lbool(int v) : value(v) { }

public:
    lbool()       : value(0) { }
    lbool(bool x) : value((int)x*2-1) { }
    int toInt(void) const { return value; }

    bool  operator == (lbool b) const { return value == b.value; }
    bool  operator != (lbool b) const { return value != b.value; }
    lbool operator ^ (bool b) const { return b ? lbool(-value) : lbool(value); }

    friend int   toInt  (lbool l);
    friend lbool toLbool(int   v);
};
inline int   toInt  (lbool l) { return l.toInt(); }
inline lbool toLbool(int   v) { return lbool(v);  }

const lbool l_True  = toLbool( 1);
const lbool l_False = toLbool(-1);
const lbool l_Undef = toLbool( 0);

//=================================================================================================
// Clause -- a simple class for representing a clause:


class Clause {
    uint32_t size_etc;
    union { float act; uint32_t abst; } extra;
    Lit     data[0];

public:
    void calcAbstraction() {
        uint32_t abstraction = 0;
        for (int i = 0; i < size(); i++)
            abstraction |= 1 << (var(data[i]) & 31);
        extra.abst = abstraction;  }

    // NOTE: This constructor cannot be used directly (doesn't allocate enough memory).
    template<class V>
    Clause(const V& ps, bool learnt) {
        size_etc = (ps.size() << 3) | (uint32_t)learnt;
        for (int i = 0; i < ps.size(); i++) data[i] = ps[i];
        if (learnt) extra.act = 0; else calcAbstraction(); }

    // -- use this function instead:
    template<class V>
    friend Clause* Clause_new(const V& ps, bool learnt = false) {
        assert(sizeof(Lit)      == sizeof(uint32_t));
        assert(sizeof(float)    == sizeof(uint32_t));
        void* mem = malloc(sizeof(Clause) + sizeof(uint32_t)*(ps.size()));
        if(mem==NULL) throw memOVERFLOW;
        return new (mem) Clause(ps, learnt); }

    int          size        ()      const   { return size_etc >> 3; }
    void         shrink      (int i)         { assert(i <= size()); size_etc = (((size_etc >> 3) - i) << 3) | (size_etc & 7); }
    void         pop         ()              { shrink(1); }
    bool         learnt      ()      const   { return size_etc & 1; }
    uint32_t     mark        ()      const   { return (size_etc >> 1) & 3; }
    void         mark        (uint32_t m)    { size_etc = (size_etc & ~6) | ((m & 3) << 1); }
    const Lit&   last        ()      const   { return data[size()-1]; }

    // NOTE: somewhat unsafe to change the clause in-place! Must manually call 'calcAbstraction' afterwards for
    //       subsumption operations to behave correctly.
    Lit&         operator [] (int i)         { return data[i]; }
    Lit          operator [] (int i) const   { return data[i]; }
    operator const Lit* (void) const         { return data; }

    float&       activity    ()              { return extra.act; }
    uint32_t     abstraction () const { return extra.abst; }

    Lit          subsumes    (const Clause& other) const;
    void         strengthen  (Lit p);
};


/*_________________________________________________________________________________________________
|
|  subsumes : (other : const Clause&)  ->  Lit
|  
|  Description:
|       Checks if clause subsumes 'other', and at the same time, if it can be used to simplify 'other'
|       by subsumption resolution.
|  
|    Result:
|       lit_Error  - No subsumption or simplification
|       lit_Undef  - Clause subsumes 'other'
|       p          - The literal p can be deleted from 'other'
|________________________________________________________________________________________________@*/
inline Lit Clause::subsumes(const Clause& other) const
{
    if (other.size() < size() || (extra.abst & ~other.extra.abst) != 0)
        return lit_Error;

    Lit        ret = lit_Undef;
    const Lit* c  = (const Lit*)(*this);
    const Lit* d  = (const Lit*)other;

    for (int i = 0; i < size(); i++) {
        // search for c[i] or ~c[i]
        for (int j = 0; j < other.size(); j++)
            if (c[i] == d[j])
                goto ok;
            else if (ret == lit_Undef && c[i] == ~d[j]){
                ret = c[i];
                goto ok;
            }

        // did not find it
        return lit_Error;
    ok:;
    }

    return ret;
}


inline void Clause::strengthen(Lit p)
{
    remove(*this, p);
    calcAbstraction();
}

typedef char AggrType;
const AggrType SUM  = 0; // NOTE: CARD = (SUM with weights =1).
const AggrType PROD = 1;
const AggrType MIN  = 2;
const AggrType MAX  = 3;
const int NB_AGGR_TYPES = 4;

typedef char Occurrence;
const Occurrence DEFN = 0;
const Occurrence POS  = 1;
const Occurrence NEG  = 2;

inline Occurrence relativeOccurrence(Occurrence o, Lit l) {
    if (o==DEFN) return DEFN;
    if (o==POS)  return sign(l)? NEG : POS;
    else         return sign(l)? POS : NEG;
}

/**
 * if lower, then c <=> bound =< #set
 * else then c <=> #set =< bound
 */
struct AggrExpr {
	AggrType type;
	int	bound, currentmin, currentmax; //current keeps the currently derived min and max bounds
	bool lower;
    Lit	head;
    AggrSet* set;

    AggrExpr(bool lower, int bound, Lit head, AggrType type, AggrSet* set) :
    	type(type), bound(bound), set(set), lower(lower), head(head) {}
};
struct AggrSet {
    struct WLit {  // Weighted literal
    	Lit	lit;
		int	weight;

        WLit(Lit l, int w) : lit(l), weight(w) {}
    };
    struct PropagationInfo {          // Propagated literal
        Lit         lit;              // value(lit)==l_True.
        int         weight;
        Occurrence  type;

        PropagationInfo(Lit l, int w, Occurrence t) : lit(l), weight(w), type(t) {}
    };

    vec<WLit>	wlitset;			// Stores the actual set of weighted literals.
    int			cmax;				// (constant) sum of all weights / set.size(). Not used when type==MIN or MAX.
    vec<AggrExpr*>  exprs;			// In which expressions does this set occur. NOTE: there's no point in splitting this in "already satisfied" and "not yet satisfied"; we can't avoid doing most of the propagation work anew.
    vec<PropagationInfo> stack;		// Stack of propagations of this set's expressions so far.

    AggrSet(): min(0), max(0){};
};

struct AggrWatch {
    AggrSet*        set;
    Occurrence      type;
    AggrExpr*       expr;             // Not used (NULL) if type!=DEFN
    int             index;            // Not used if type==DEFN

    AggrWatch(AggrSet* s, AggrExpr* e, int i, Occurrence t = DEFN) : set(s), type(t), expr(e), index(i) {}
};
struct AggrReason {                   // Needed to build (with implicitReasonClause(Lit)) a reason clause for a cardinality propagation.
    AggrExpr*       expr;
    AggrSet*        set;
    Occurrence      type;

    AggrReason(AggrExpr* e, AggrSet* s, Occurrence t) : expr(e), set(s), type(t) {}
};

inline int compare_WLits(const void* a, const void* b) {
    AggrSet::WLit* arg1 = (AggrSet::WLit*)a;
    AggrSet::WLit* arg2 = (AggrSet::WLit*)b;
    if (arg1->weight < arg2->weight) return -1;
    else if (arg1->weight == arg2->weight) return 0;
    else return 1;
}    

class Rule {
    uint32_t size_etc;
    Lit     data[0];

public:
    // NOTE: This constructor cannot be used directly (doesn't allocate enough memory).
    template<class V>
    Rule(const V& ps) {
        size_etc = (ps.size() << 3);
        for (int i = 0; i < ps.size(); i++) data[i] = ps[i]; }

    // -- use this function instead:
    template<class V>
    friend Rule* Rule_new(const V& ps) {
        assert(sizeof(Lit)      == sizeof(uint32_t));
        void* mem = malloc(sizeof(Rule) + sizeof(uint32_t)*(ps.size()));
        if(mem==NULL) throw memOVERFLOW;
        return new (mem) Rule(ps); }

    int          size        ()      const   { return size_etc >> 3; }

    // NOTE: somewhat unsafe to change the clause in-place! Must manually call 'calcAbstraction' afterwards for
    //       subsumption operations to behave correctly.
    Lit&     operator [] (int i)         { return data[i]; }
    Lit      operator [] (int i) const   { return data[i]; }
    operator const Lit* (void) const         { return data; }
};

#endif
