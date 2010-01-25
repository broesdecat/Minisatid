#ifndef DEBUG_H
#define DEBUG_H
#include <stdarg.h>
#include <string.h>

#define DEFAULTOUTPUT 1
#define LONGOUTPUT 2
#define UNFOUNDEDOUTPUT 3

#if defined(NDEBUG)
	#define pmesg(level, format, args...) ((void)0)
#else
	void pmesg(int level, const char* format, ...);
#endif

#endif /* DEBUG_H */
