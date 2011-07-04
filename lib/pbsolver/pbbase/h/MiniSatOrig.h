#ifndef MINISATORIG_H
#define MINISATORIG_H

#include "Int.h"

namespace MiniSatPP {
SearchMetaData* optimizeBase(vec<Int>& seq, vec<Int>& rhs, int& cost_bestfound, vec<int>& base_bestfound,unsigned int weights[][2],int length,unsigned int cutoff);
}
#endif /*MINISATORIG_H*/


