#include "PbParser.h"
#include "File.h"


//=================================================================================================
// Parser buffers (streams):

namespace MiniSatPP {

class FileBuffer {
    File    in;
    int     next;
public:
    int     line;
    FileBuffer(cchar* input_file) : in(input_file, "rb") {
        if (in.null()) reportf("ERROR! Could not open file for reading: %s\n", input_file), exit(0);
        next = in.getCharQ();
        line = 1; }
   ~FileBuffer() {}
    int  operator *  () { return next; }
    void operator ++ () { if (next == '\n') line++; next = in.getCharQ(); }
};


class StringBuffer {
    cchar*  ptr;
    cchar*  last;
public:
    int     line;
    StringBuffer(cchar* text)           { ptr = text; last = ptr + strlen(text); line = 1; }
    StringBuffer(cchar* text, int size) { ptr = text; last = ptr + size; line = 1; }
   ~StringBuffer() {}
    int  operator *  () { return (ptr >= last) ? EOF : *ptr; }
    void operator ++ () { if (*ptr == '\n') line++; ++ptr; }
};



//=================================================================================================
// PB Parser:


/*
The 'B' (parser Buffer) parameter should implement:
    
    operator *      -- Peek at current token. Should return a character 0-255 or 'EOF'.
    operator ++     -- Advance to next token.
    line            -- Public member variable.

The 'S' (Solver) parameter should implement:

    void allocConstrs(int n_vars, int n_constrs)
        -- Called before any of the below methods. Sets the size of the problem.

    int  getVar(cchar* name)
        -- Called during parsing to convert string names to indices. Ownership of 'name' 
        remains with caller (the string should be copied).

    void addGoal(const vec<Lit>& ps, const vec<Int>& Cs)
        -- Called before any constraint is adde to establish goal function:
                "minimize( Cs[0]*ps[0] + ... + Cs[n-1]*ps[n-1] )"

    bool addConstr(const vec<Lit>& ps, const vec<Int>& Cs, Int rhs, int ineq)
        -- Called when a constraint has been parsed. Constraint is of type:
                "Cs[0]*ps[0] + ... + Cs[n-1]*ps[n-1] >= rhs" ('rhs'=right-hand side). 
        'ineq' determines the inequality used: -2 for <, -1 for <=, 0 for ==, 1 for >=, 2 for >. 
        Should return TRUE if successful, FALSE if conflict detected.
*/


template<class B>
static void skipWhitespace(B& in) {     // not including newline
    while (*in == ' ' || *in == '\t')
        ++in; }

template<class B>
static void skipLine(B& in) {
    for (;;){
        if (*in == EOF) return;
        if (*in == '\n') { ++in; return; }
        ++in; } }

template<class B>
static void skipComments(B& in) {      // skip comment and empty lines (assuming we are at beginning of line)
    while (*in == '*' || *in == '\n') skipLine(in); }

template<class B>
static bool skipEndOfLine(B& in) {     // skip newline AND trailing comment/empty lines
    if (*in == '\n') ++in;
    else             return false;
    skipComments(in);
    return true; }

template<class B>
static bool skipText(B& in, cchar* text) {
    while (*text != 0){
        if (*in != *text) return false;
        ++in, ++text; }
    return true; }

template<class B>
static Int parseInt(B& in) {
    Int     val(0);
    bool    neg = false;
    skipWhitespace(in);
    if      (*in == '-') neg = true, ++in;
    else if (*in == '+') ++in;
    skipWhitespace(in);     // BE NICE: allow "- 3" and "+  4" etc.
    if (*in < '0' || *in > '9')
        throw nsprintf("Expected digit, not: %c", *in);
    while (*in >= '0' && *in <= '9'){
      #ifdef NO_GMP
        val *= 2;
        if (val < 0 || val > Int(9223372036854775807LL >> 20)) throw xstrdup("Integer overflow. Use BigNum-version.");      // (20 extra bits should be enough...)
        val *= 5;
      #else
        val *= 10;
      #endif
        val += (*in - '0');
        ++in; }
    return neg ? -val : val; }

template<class B>
static char* parseIdent(B& in, vec<char>& tmp) {   // 'tmp' is cleared, then filled with the parsed string. '(char*)tmp' is returned for convenience.
    skipWhitespace(in);
    if ((*in < 'a' || *in > 'z') && (*in < 'A' || *in > 'Z') && *in != '_') throw nsprintf("Expected start of identifier, not: %c", *in);
    tmp.clear();
    tmp.push(*in);
    ++in;
    while ((*in >= 'a' && *in <= 'z') || (*in >= 'A' && *in <= 'Z') || (*in >= '0' && *in <= '9') || *in == '_')
        tmp.push(*in),
        ++in;
    tmp.push(0);
    return (char*)tmp; }


template<class B, class S>
void parseExpr(B& in, S& solver, vec<Lit>& out_ps, vec<Int>& out_Cs, vec<char>& tmp)
    // NOTE! only uses "getVar()" method of solver; doesn't add anything.
    // 'tmp' is a tempory, passed to avoid frequent memory reallocation.
{
    bool empty = true;
    for(;;){
        skipWhitespace(in);
        if ((*in < '0' || *in > '9') && *in != '+' && *in != '-') break;
        out_Cs.push(parseInt(in));
        skipWhitespace(in);
        if (opt_star_in_input) {
            if (*in != '*') throw xstrdup("Missing '*' after coefficient.");
            ++in;
        }
        out_ps.push(Lit(solver.getVar(parseIdent(in, tmp))));
        empty = false;
    }
    if (empty) throw xstrdup("Empty expression.");
}


template<class B, class S>
void parseSize(B& in, S& solver)
{
    int n_vars, n_constrs;

    if (*in != '*') return;
    ++in;
    skipWhitespace(in);

    if (!skipText(in, "#variable=")) goto Abort;
    n_vars = toint(parseInt(in));

    skipWhitespace(in);
    if (!skipText(in, "#constraint=")) goto Abort;
    n_constrs = toint(parseInt(in));

    solver.allocConstrs(n_vars, n_constrs);

  Abort:
    skipLine(in);
    skipComments(in);
}

template<class B, class S>
void parseGoal(B& in, S& solver)
{
    skipWhitespace(in);
    if (!skipText(in, "min:")) return;      // No goal specified. If file is syntactically correct, no characters will have been consumed (expecting integer).

    vec<Lit> ps; vec<Int> Cs; vec<char> tmp;
    skipWhitespace(in);
    if (*in == ';'){
        ++in;
        skipLine(in);
    }else{
        parseExpr(in, solver, ps, Cs, tmp);
        skipWhitespace(in);
        if (!skipText(in, ";")) throw xstrdup("Expecting ';' after goal function.");
    }
    skipEndOfLine(in);

    solver.addGoal(ps, Cs);
}

template<class B>
int parseInequality(B& in)
{
    int ineq;
    skipWhitespace(in);
    if (*in == '<'){
        ++in;
        if (*in == '=') ineq = -1, ++in;
        else            ineq = -2;
    }else if (*in == '>'){
        ++in;
        if (*in == '=') ineq = +1, ++in;
        else            ineq = +2;
    }else{
        if (*in == '='){
            ++in;
            if (*in == '=') ++in;
            ineq = 0;
        }else
            throw nsprintf("Expected inequality, not: %c", *in);
    }
    return ineq;
}

template<class B, class S>
bool parseConstrs(B& in, S& solver)
{
    vec<Lit> ps; vec<Int> Cs; vec<char> tmp;
    int     ineq;
    Int     rhs;
    while (*in != EOF){
        parseExpr(in, solver, ps, Cs, tmp);
        ineq = parseInequality(in);
        rhs  = parseInt(in);

        skipWhitespace(in);
        if (!skipText(in, ";")) throw xstrdup("Expecting ';' after constraint.");
        skipEndOfLine(in);

        if (!solver.addConstr(ps, Cs, rhs, ineq,false))
            return false;
        ps.clear();
        Cs.clear();
    }
    return true;
}


//=================================================================================================
// Main parser functions:


template<class B, class S>
static bool parse_PB(B& in, S& solver, bool abort_on_error)
{
    try{
        parseSize(in, solver);
        parseGoal(in, solver);
        return parseConstrs(in, solver);
    }catch (cchar* msg){
        if (abort_on_error){
            reportf("PARSE ERROR! [line %d] %s\n", in.line, msg);
            xfree(msg);
            if (opt_satlive && !opt_try)
                printf("s UNKNOWN\n");
            exit(opt_try ? 5 : 0);
        }else
            throw msg;
    }

}

// PB parser functions: Returns TRUE if successful, FALSE if conflict detected during parsing.
// If 'abort_on_error' is false, a 'cchar*' error message may be thrown.
//
void parse_PB_file(cchar* filename, PbSolver& solver, bool abort_on_error) {
    FileBuffer buf(filename);
    parse_PB(buf, solver, abort_on_error); }

void parse_PB(cchar* text, PbSolver& solver, bool abort_on_error) {
    StringBuffer buf(text);
    parse_PB(buf, solver, abort_on_error); }


// yay prototypes
template<class B, class S>
bool parseList(B& in, S& solver);

template<class B, class S>
void parseListExpr(B& in, S& solver, vec<Lit>& out_ps, vec<Int>& out_Cs, vec<char>& tmp);

void parse_natlist_file(cchar* filename, PbSolver& solver,bool abort_on_error) {
    FileBuffer buf(filename);
    parseList(buf, solver); }



//*********************************************************

template<class B, class S>
bool parseList(B& in, S& solver)
{
    vec<Lit> ps; vec<Int> Cs; vec<char> tmp;
    Int     rhs;
    parseListExpr(in, solver, ps, Cs, tmp);
    int size = Cs.size();
    solver.allocConstrs(size, 1);
    for (int i = 0; i < size; ++i) {
        vec<char> tmp;
        tmp.push('x');
        int xj = i;
        vec<int> xjd;
        if (xj==0)
        	xjd.push(0);
        else {
	        for(int j=0; xj!=0 ; j++) {
	        	xjd.push(xj % 10);
	        	xj = xj / 10;
	        }
	    }
        for(int j=xjd.size()-1;j>=0;j--){
        	if (xjd[j]==0) tmp.push('0');
        	else if (xjd[j]==1) tmp.push('1');
        	else if (xjd[j]==2) tmp.push('2');
        	else if (xjd[j]==3) tmp.push('3');
        	else if (xjd[j]==4) tmp.push('4');
        	else if (xjd[j]==5) tmp.push('5');
        	else if (xjd[j]==6) tmp.push('6');
        	else if (xjd[j]==7) tmp.push('7');
        	else if (xjd[j]==8) tmp.push('8');
        	else if (xjd[j]==9) tmp.push('9');
        }
        tmp.push(0);
        ps.push(Lit(solver.getVar((char*)tmp)));
    }

    // arbitrary, but fixed choice for the RHS,
    // which /should/ be irrelevant for the optimal base computations;
    // setting it to a value > 1 /should/ make sure that normalization
    // does not do its thing
    Int RHS_CONST = Int(2147483647);
    solver.addConstr(ps, Cs, RHS_CONST, 1,true);
    return true;
}

// parse anything like ('Int' ',')^* 'Int' ';'
template<class B, class S>
void parseListExpr(B& in, S& solver, vec<Lit>& out_ps, vec<Int>& out_Cs, vec<char>& tmp)
    // 'tmp' is a tempory, passed to avoid frequent memory reallocation.
{
    bool empty = true;
    bool done = false;
    while (*in != EOF){
        skipWhitespace(in);
        if ((*in < '0' || *in > '9') && *in != '+' && *in != '-') break;
        empty = false;
        out_Cs.push(parseInt(in));
        skipWhitespace(in);
        if (*in == ';') {
            done = true;
            break;
        }
        else if (*in != ',') throw xstrdup("Missing ',' after number.");
        ++in;
    }

    // the following line contains an ugly quickfix for no output
    // being produced on lists of only 1 element: duplicate that element!
    if (out_Cs.size() == 1) out_Cs.push(out_Cs[0]);

    if (empty) throw xstrdup("Empty list!");
    if (!done) throw xstrdup("Premature end of input!");
}

}


//=================================================================================================
// Debug:


#if 0
#include "Debug.h"
#include "Map.h"

namespace MiniSatPP {
#define Solver DummySolver

struct DummySolver {
    Map<cchar*, int> name2index;
    vec<cchar*>      index2name;

    int getVar(cchar* name) {
        int ret;
        if (!name2index.peek(name, ret)){
            index2name.push(xstrdup(name));
            ret = name2index.set(index2name.last(), index2name.size()-1); }
        return ret; }

    void alloc(int n_vars, int n_constrs) {
        printf("alloc(%d, %d)\n", n_vars, n_constrs); }
    void addGoal(vec<Lit>& ps, vec<Int>& Cs) {
        printf("MIN: "); dump(ps, Cs); printf("\n"); }
    bool addConstr(vec<Lit>& ps, vec<Int>& Cs, Int rhs, int ineq) {
        static cchar* ineq_name[5] = { "<", "<=" ,"==", ">=", ">" };
        printf("CONSTR: "); dump(ps, Cs); printf(" %s ", ineq_name[ineq+2]); dump(rhs); printf("\n");
        return true; }
};

void test(void)
{
    DummySolver     solver;
    debug_names = &solver.index2name;
    parseFile_PB("test.pb", solver, true);
}
}
#endif
