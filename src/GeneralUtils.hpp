#ifndef GENERALUTILS_HPP_
#define GENERALUTILS_HPP_

#include <vector>
#include <map>
#include <exception>
#include <string>
#include <assert.h>
#include <iostream>

//FIXME move to print headers
#define report(...) ( fflush(stdout), fprintf(stderr, __VA_ARGS__), fflush(stderr) )

namespace MinisatID {
	///////
	// Measuring cpu time
	///////

	//In elapsed seconds, making abstraction of other processes running on the system
	double cpuTime(void);

	///////
	// Generic system exception
	///////

	class idpexception: public std::exception{
	private:
		std::string mess;

	public:
		idpexception(const char* m): std::exception(){
			mess.append("Exception caught: ");
			mess.append(m);
		}

		~idpexception() throw(){}

		virtual const char* what() const throw(){
			return mess.c_str();
		}
	};
}

///////
// Weight declaration and utilities
///////

#ifdef GMP
	#include "gmpxx.h"

	namespace MinisatID {
	class Weight{
	private:
		mpz_class w;
		bool inf, pos;
	public:
		Weight(): w(0), inf(false), pos(false){}
		Weight(int i): w(i), inf(false), pos(false){}
		Weight(long i): w(i), inf(false), pos(false){}
		Weight(mpz_class w): w(w), inf(false), pos(false){}
		Weight(bool posinf): w(0), inf(true), pos(posinf){}

		operator const mpz_class&() const { assert(!inf); return w; }

		std::string get_str() const{
			if(!inf){
				return w.get_str();
			}else{
				return pos?"+inf":"-inf";
			}
		}

		friend std::ostream& operator<<(std::ostream& output, const Weight& p);
		friend std::istream& operator>>(std::istream& input, Weight& obj);

		const Weight operator-() const {
			Weight w2(*this);
			w2.w = -w2.w;
			w2.pos=!w2.pos;
			return w2;
		}

		const Weight operator-(const Weight &other) const {
			return Weight(*this) -= other;
		}

		const Weight operator+(const Weight &other) const {
			return Weight(*this) += other;
		}

		const Weight operator*(const Weight &other) const {
			return Weight(*this) *= other;
		}

		const Weight operator/(const Weight &other) const {
			return Weight(*this) /= other;
		}

		Weight& operator+=(const Weight &rhs) {
			if(rhs.inf || inf){
				assert(!rhs.inf || !inf);
				w=0;
				pos = inf?pos:rhs.pos;
				inf = true;
			}else{
				w += rhs.w;
			}
			return *this;
		}

		Weight& operator-=(const Weight &rhs) {
			if(rhs.inf || inf){
				assert(!rhs.inf || !inf);
				w=0;
				pos = inf?pos:!rhs.pos;
				inf = true;
			}else{
				w -= rhs.w;
			}
			return *this;
		}

		Weight& operator*=(const Weight &rhs) {
			if(rhs.inf || inf){
				assert(!rhs.inf || !inf);
				w=0;
				pos = inf?pos:rhs.pos;
				inf = true;
			}else{
				w *= rhs.w;
			}
			return *this;
		}

		Weight& operator/=(const Weight &rhs) {
			if(rhs.inf || inf){
				assert(!rhs.inf || !inf);
				if(inf){
					if(rhs.w<0){
						pos = !pos;
					}
				}else{
					w = 0;
					inf = false;
				}
			}else{
				w /= rhs.w;
			}
			return *this;
		}

		bool operator==(const Weight& weight) const{
			return w==weight.w && inf==weight.inf && pos==weight.pos;
		}

		bool operator!=(const Weight& weight) const{
			return !(*this==weight);
		}

		bool operator<(const Weight& weight) const {
			if(!inf && !weight.inf){
				return w < weight.w;
			}else if(inf){
				if(weight.inf){
					return false;
				}else{
					return !pos;
				}
			}else{//only weight is inf
				return weight.pos;
			}
		}

		bool operator<=(const Weight& weight) const{
			return *this==weight || *this<weight;
		}

		bool operator>(const Weight& weight) const{
			return !(*this<=weight);
		}

		bool operator>=(const Weight& weight) const{
			return !(*this<weight);
		}
	};
	Weight abs(const Weight& w);
	std::ostream& operator<<(std::ostream& output, const Weight& p);
	std::istream& operator>>(std::istream& input, Weight& obj);
	}
#else
	namespace MinisatID {
	#define NOARBITPREC
	typedef long Weight;
	//FAST, NO OVERFLOW SUPPORT
	}
#endif


namespace MinisatID {
	Weight posInfinity();
	Weight negInfinity();

	std::string toString(const Weight& w);

	///////
	// Comparison operators
	///////

	enum EqType{ MEQ, MNEQ, ML, MG, MGEQ, MLEQ };

	///////
	// Aggregate specification operators
	///////

	enum AggType 	{ SUM, PROD, MIN, MAX, CARD }; 	// Type of aggregate concerned
	//FIXME correct notion of upper and lower bound!
	enum AggSign 	{ AGGSIGN_UB, AGGSIGN_LB}; 	// Sign of the bound of the aggregate
	enum AggSem 	{ COMP, DEF, IMPLICATION };	// Semantics of satisfiability of the aggregate head: COMPletion or DEFinitional

	///////
	// Definitional options
	///////

	enum DEFFINDCS { always, adaptive, lazy };	// Unfounded set search frequency
	enum DEFMARKDEPTH { include_cs };			// Originally also contained stop_at_cs, which is no longer correct
												// when a guaranteed cycle-free justification is used!
	enum DEFSEARCHSTRAT { breadth_first, depth_first }; // Unfounded set search strategy
	enum DEFSEM { DEF_STABLE, DEF_WELLF, DEF_COMP }; 				// Definitional semantics

	enum POLARITY {
		POL_TRUE,
		POL_FALSE,
		POL_STORED,
		POL_RAND
	}; // SAT-solver polarity option

	enum INPUTFORMAT {FORMAT_FODOT, FORMAT_ASP, FORMAT_OPB};
	enum OUTPUTFORMAT { TRANS_FODOT, TRANS_ASP, TRANS_PLAIN };

	// Structure containing general options for the solvers
	class SolverOption {
	public:
		INPUTFORMAT format;
		OUTPUTFORMAT transformat;
		int verbosity;
		int nbmodels; //Try to find at most this number of models
		bool printcnfgraph;
		DEFSEM defsem;
		DEFSEARCHSTRAT ufs_strategy;
		DEFFINDCS defn_strategy;
		DEFMARKDEPTH defn_search;
		int idclausesaving, aggclausesaving;
		bool selectOneFromUFS;
		bool pbsolver;
		bool watchedagg;
		std::string primesfile;
		bool remap;
		double rand_var_freq, var_decay;
		POLARITY polarity;
		bool bumpaggonnotify, bumpidonstart, subsetminimizeexplanation, asapaggprop;
		long ufsvarintrothreshold;

		SolverOption();

		void print();
	};

	///////
	// Support for deleting lists of pointer elements
	///////

	template<class T>
	void deleteList(std::vector<T*> l){
		for(class std::vector<T*>::const_iterator i=l.begin(); i!=l.end(); i++){
			if(*i!=NULL){
				delete(*i);
			}
		}
		l.clear();
	}

	template<class T>
	void deleteList(std::vector<std::vector<T*> > l){
		for(class std::vector<std::vector<T*> >::const_iterator i=l.begin(); i!=l.end(); i++){
			deleteList(*i);
		}
		l.clear();
	}

	template<class T, class K>
	void deleteList(std::map<K, T*> l){
		for(class std::map<K, T*>::const_iterator i=l.begin(); i!=l.end(); i++){
			if((*i).second!=NULL){
				delete((*i).second);
			}
		}
		l.clear();
	}

}


#endif /* GENERALUTILS_HPP_ */
