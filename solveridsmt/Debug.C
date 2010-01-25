#include "Debug.h"
#include <stdio.h>

extern int msglevel; /* the higher, the more messages... */

#ifdef NDEBUG
	/* Empty body, so a good compiler will optimise calls
	   to pmesg away */
#else
void pmesg(int level, const char* format, ...) {
	va_list args;

	if (level>msglevel){
		return;
	}

	va_start(args, format);
	vfprintf(stderr, format, args);
	va_end(args);
}
#endif /* NDEBUG */
