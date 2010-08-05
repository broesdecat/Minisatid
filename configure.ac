AC_INIT([minisatid],[3.1],[krr@cs.kuleuven.be])
AC_PROG_CXX
AC_DECL_YYTEXT
#AC_PROG_LEX
AC_PROG_YACC
AM_INIT_AUTOMAKE([-Wall foreign subdir-objects])  #-ffloat-store  -Wextra -Wno-unused-parameter -pedantic
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
AC_SUBST([AM_CXXFLAGS])
AC_SUBST([AM_YFLAGS])
AC_SUBST([AM_LFLAGS])
AC_SUBST([AM_LDFLAGS])
AC_SUBST([LIBS])

SD_CXXFLAGS="-ffloat-store -Wextra -Wno-unused-parameter -Wno-variadic-macros -Wno-format -pedantic -Wall -Wno-variadic-macros -Wreturn-type "
SD_LDFLAGS=

AC_ARG_ENABLE([build],
[  --enable-build    Turn on debugging (debug), profiling (profile), release version(release), static release version (static) or code cover building (codecover)],
[case "${enableval}" in
  debug)   SD_CXXFLAGS+="-O0 -ggdb -D DEBUG " SD_LDFLAGS+="-ggdb " ;;
  profile) SD_CXXFLAGS+="-O3 -pg -ggdb -D NDEBUG " SD_LDFLAGS+="-ggdb " ;;
  release) SD_CXXFLAGS+="-O3 -D NDEBUG " SD_LDFLAGS+="" ;;
  static)  SD_CXXFLAGS+="-O3 -D NDEBUG " SD_LDFLAGS+="--static " ;;
  codecover) SD_CXXFLAGS+="-O0 -fprofile-arcs -ftest-coverage -ggdb -D DEBUG " SD_LDFLAGS+="-ggdb " ;;
  *) AC_MSG_ERROR([bad value ${enableval} for --enable-build]) ;;
esac],[SD_CXXFLAGS+="-DNDEBUG $SD_CXXFLAGS -O3 " SD_LDFLAGS+="$SD_LDFLAGS "])

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
	32) SD_CXXFLAGS+=" -m32 " ;;
	64) SD_CXXFLAGS+=" -m64 ";;
	*) AC_MSG_ERROR([bad value ${enableval} for --enable-bits]) ;;
esac],[])

# Export flags
AC_SUBST([SVNDIGEST_LDFLAGS], $SD_LDFLAGS)
AC_SUBST([SVNDIGEST_CXXFLAGS], $SD_CXXFLAGS)

# files to generate via autotools (.am or .in source files)
AC_CONFIG_FILES([Makefile])

# generate the final Makefile etc.
AC_OUTPUT
