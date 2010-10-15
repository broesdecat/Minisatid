AC_INIT([minisatid],[3.2],[krr@cs.kuleuven.be])

if test x"${CXXFLAGS+set}" = xset; then 
	# the user set CXXFLAGS; don't override it. 
	CXXFLAGS+=""
else 
	CXXFLAGS=""
fi

AC_PROG_CXX
AC_DECL_YYTEXT
#AC_PROG_LEX
AC_PROG_YACC
AM_INIT_AUTOMAKE([foreign subdir-objects])  #-ffloat-store OTHER parameters like pedantic, seem no to work here, I set them in debug CXXflags!
#AM_SILENT_RULES([yes]) from 1.11 on
AC_LANG([C++])

#check for the necessary headers
AC_HEADER_STDC
AC_CHECK_HEADERS([string])
AC_CHECK_HEADERS([vector])
AC_CHECK_HEADERS([set])
AC_CHECK_HEADERS([map])
AC_CHECK_HEADERS([cstdlib])
AC_CHECK_HEADERS([limits])
AC_CHECK_HEADERS([assert])
AC_CHECK_HEADERS([cmath])
AC_CHECK_HEADERS([iostream])
AC_CHECK_HEADERS([tr1/memory])

# Checks for typedefs, structures, and compiler characteristics.
AC_TYPE_SIZE_T

# distribute additional compiler and linker flags
# --> set these variables instead of CXXFLAGS or LDFLAGS
AC_SUBST([LIBS])

CXXFLAGS+="-ffloat-store -Wall -Wextra -pedantic "
LDFLAGS+=

AC_ARG_ENABLE([build],
[  --enable-build    Turn on debugging (debug), profiling (profile), release version(release), static release version (static) or code cover building (codecover)],
[case "${enableval}" in
  debug)   CXXFLAGS+="-O0 -ggdb -D DEBUG -Wno-unused-parameter " LDFLAGS+="-ggdb " ;;
  profile) CXXFLAGS+="-O3 -pg -ggdb -D NDEBUG " LDFLAGS+="-ggdb " ;;
  release) CXXFLAGS+="-O3 -D NDEBUG " LDFLAGS+="" ;;
  static)  CXXFLAGS+="-O3 -D NDEBUG " LDFLAGS+="--static " ;;
  codecover) CXXFLAGS+="-O0 -fprofile-arcs -ftest-coverage -ggdb -D DEBUG " LDFLAGS+="-ggdb " ;;
  *) AC_MSG_ERROR([bad value ${enableval} for --enable-build]) ;;
esac],[CXXFLAGS+="-DNDEBUG $SD_CXXFLAGS -O3 " LDFLAGS+="$SD_LDFLAGS "])

AC_ARG_ENABLE([sat],
[  --enable-sat    Use minisat 2.0b(old), minisat 09z(hack) or minisat 2.2(new)],
[case "${enableval}" in
  old)   oldm=true
		 hackm=false
  		 newm=false
  		 ;;
  hack)  oldm=false
		 hackm=true
  		 newm=false
  		;;
  new)   oldm=false
		 hackm=false
  		 newm=true
		;;
  *) AC_MSG_ERROR([bad value ${enableval} for --enable-sat]) ;;
esac],[oldm=true])

AM_CONDITIONAL([USEMINISAT],[test x$oldm = xtrue])
AM_CONDITIONAL([USEMINISAT09Z],[test x$hackm = xtrue])
AM_CONDITIONAL([USEMINISAT22],[test x$newm = xtrue])

AC_ARG_ENABLE([bits],
[  --enable-bits    Turn on 32/64 bit compiling],
[case "${enableval}" in
	32) CXXFLAGS+=" -m32 " ;;
	64) CXXFLAGS+=" -m64 ";;
	*) AC_MSG_ERROR([bad value ${enableval} for --enable-bits]) ;;
esac],[])

# Export flags

# files to generate via autotools (.am or .in source files)
AC_CONFIG_FILES([Makefile])

# generate the final Makefile etc.
AC_OUTPUT
