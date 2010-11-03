/*
 * AggProp.hpp
 *
 *  Created on: Oct 26, 2010
 *      Author: broes
 */

#ifndef AGGPROP_HPP_
#define AGGPROP_HPP_

#include "solvers/utils/Utils.hpp"
#include <vector>

namespace MinisatID{

class WL;
typedef std::vector<WL> vwl;
class TypedSet;
class AggSolver;

class Agg{
private:
	Weight		bound;
	AggSign 	sign;
	Lit			head;
	AggSem		sem;
	int			index;
	bool		optim;

public:
	Agg(const Weight& bound, AggSign sign, const Lit& head, AggSem sem, bool optim = false):
		bound(bound), sign(sign), head(head), sem(sem), index(-1), optim(optim){	}

	const Lit& 	getHead		() 					const 	{ return head; }
	int			getIndex	()					const	{ return index; }
	const Weight& getBound	() 					const	{ return bound; }
	bool 		isLower		()					const	{ return sign!=UB; }
	bool 		isUpper		()					const	{ return sign!=LB; }
	bool 		isDefined	()					const	{ return sem==DEF; }
	AggSign		getSign		()					const	{ return sign; }
	bool		isOptim		()					const	{ return optim; }
	void 		setIndex	(int ind) 					{ index = ind; }
	void		setBound	(const Weight& w)			{ bound = w;}
};

class AggProp{
public:
	virtual const char*	getName					() 										const = 0;
	virtual AggType 	getType					() 										const = 0;
	virtual bool 		isNeutralElement		(const Weight& w)						const = 0;
	virtual bool 		isMonotone				(const Agg& agg, const WL& l) 			const = 0;
	virtual Weight 		getBestPossible			(TypedSet* set) 						const = 0;
	virtual Weight 		getCombinedWeight		(const Weight& one, const Weight& two) 	const = 0;
	virtual WL 			handleOccurenceOfBothSigns(const WL& one, const WL& two, TypedSet* set) = 0;
};

class MaxProp: public AggProp{
public:
	const char* getName					() 										const { return "MAX"; }
	AggType 	getType					() 										const { return MAX; }
	bool 		isNeutralElement		(const Weight& w) 						const { return false; }
	bool 		isMonotone				(const Agg& agg, const WL& l) 			const;
	Weight 		getBestPossible			(TypedSet* set) 						const;
	Weight 		getCombinedWeight		(const Weight& one, const Weight& two) 	const;
	WL 			handleOccurenceOfBothSigns(const WL& one, const WL& two, TypedSet* set);
};

class SPProp: public AggProp{
public:
	virtual Weight	add					(const Weight& lhs, const Weight& rhs) 	const = 0;
	virtual Weight	remove				(const Weight& lhs, const Weight& rhs) 	const = 0;
};

class ProdProp: public SPProp{
public:
	const char* getName					() 										const { return "PROD"; }
	AggType 	getType					() 										const { return PROD; }
	bool 		isNeutralElement		(const Weight& w) 						const { return w==1; }
	bool 		isMonotone				(const Agg& agg, const WL& l) 			const;
	Weight		add						(const Weight& lhs, const Weight& rhs) 	const;
	Weight		remove					(const Weight& lhs, const Weight& rhs) 	const;
	Weight 		getBestPossible			(TypedSet* set) 						const;
	Weight 		getCombinedWeight		(const Weight& one, const Weight& two) 	const;
	WL 			handleOccurenceOfBothSigns(const WL& one, const WL& two, TypedSet* set);
};

class SumProp: public SPProp{
public:
	const char* getName					() 										const { return "SUM"; }
	AggType 	getType					() 										const { return SUM; }
	bool 		isNeutralElement		(const Weight& w) 						const { return w==0; }
	bool 		isMonotone				(const Agg& agg, const WL& l) 			const;
	Weight		add						(const Weight& lhs, const Weight& rhs) 	const;
	Weight		remove					(const Weight& lhs, const Weight& rhs) 	const;
	Weight 		getBestPossible			(TypedSet* set) 						const;
	Weight 		getCombinedWeight		(const Weight& one, const Weight& two) 	const;
	WL 			handleOccurenceOfBothSigns(const WL& one, const WL& two, TypedSet* set);
};

class CardProp: public SumProp{
public:
	const char* getName					() 										const { return "CARD"; }
	AggType		getType					() 										const { return CARD; }
	Weight		add						(const Weight& lhs, const Weight& rhs) 	const;
	Weight		remove					(const Weight& lhs, const Weight& rhs) 	const;
	Weight 		getBestPossible			(TypedSet* set) 						const;
	Weight 		getCombinedWeight		(const Weight& one, const Weight& two) 	const;
	WL 			handleOccurenceOfBothSigns(const WL& one, const WL& two, TypedSet* set);
};

class AggSet{
private:
	vwl	wlits;
	std::vector<Agg*> aggs;

public:
    AggSet(const std::vector<WL>& wl);

    const 	vwl& 	getWL()	const						{ return wlits; }
			void 	setWL(const std::vector<WL>& newset);
};

class Propagator;

class TypedSet{
protected:
	Weight 	esv;
	vwl 	wl;

	AggProp* 	type;

	std::vector<Agg*> 	aggregates;	//OWNS the pointers
	AggSolver*			aggsolver;	//does NOT own this pointer
	Propagator* 		prop;		//OWNS pointer

public:
	virtual ~TypedSet();

	AggSolver * const getSolver		()			const	{ return aggsolver; }
	const vwl&		getWL			()			const 	{ return wl; }

	const std::vector<Agg*>& getAgg	()		 	const	{ return aggregates; }
	std::vector<Agg*>&		getRefAgg() 				{ return aggregates; }
	void 			addAgg			(Agg* aggr);

	const Weight& 	getESV			() 			const 	{ return esv; }
	void 			setESV			(const Weight& w)	{ esv = w; }

	void 			setProp			(Propagator* p) 	{ prop = p; }
	Propagator*		getProp			() 			const { return prop; }

	/*
	void 			initialize(bool& unsat, bool& sat);
	///////
	// SEARCH
	///////

	void newDecisionLevel();
	void backtrackDecisionLevel();

	virtual bool canJustifyHead	(const Agg& agg, vec<Lit>& jstf, vec<Var>& nonjstf, vec<int>& currentjust, bool real) const = 0;
	// Propagate set literal
	rClause 	propagate		(const Lit& p, pw w);
	// Propagate head
	rClause 	propagate		(const Agg& agg);
	// Backtrack set literal
	void 		backtrack		(const Watch& w) ;
	// Backtrack head
	void 		backtrack		(const Agg& agg);

	void 		getExplanation	(vec<Lit>& lits, const AggReason& ar) const;*/
};

/*class Propagator {
protected:
	TypedSet* set; //Non-owning
public:
	Propagator(paggs agg);
	virtual ~Propagator(){};

	// Propagate set literal
	virtual rClause 	propagate		(const Lit& p, Watch* w) = 0;
	// Propagate head
	virtual rClause 	propagate		(const Agg& agg) = 0;

    virtual void 		getExplanation	(vec<Lit>& lits, const AggReason& ar) 	const = 0;

    virtual void initialize(bool& unsat, bool& sat);

    AggSolver* getSolver();
    rClause notifySolver(AggReason* reason);
};*/

}

#endif /* AGGPROP_HPP_ */
