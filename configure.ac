AC_INIT([minisatid],[3.2],[krr@cs.kuleuven.be])

#this is not an ideal solution, but it overrides the default cxxflags, so those set later are not invalid
if test -z $CXXFLAGS; then
    CXXFLAGS=" "
fi
AC_PROG_CXX
AC_DECL_YYTEXT
#AC_PROG_LEX
AC_PROG_YACC
AM_INIT_AUTOMAKE([foreign subdir-objects silent-rules]) #silent-rules FROM VERSION 1.11 #-ffloat-store OTHER parameters like pedantic, seem no to work here, I set them in debug CXXflags!
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
AC_SUBST([AC_CXXFLAGS])
AC_SUBST([AC_LDFLAGS])
AC_SUBST([LIBS])

AC_CXXFLAGS = " "
AC_LDFLAGS = " "

AC_CXXFLAGS+="-ansi -ffloat-store -Wall -Wextra -Wno-unused-parameter " 
#should use -Wno-vla to allow variable sized arrays, which pbsolver has
#its too difficult too remove them there and only remaining issue with pedantic
#but our gcc doesnt support them yet

AC_ARG_ENABLE([build],
[  --enable-build    Turn on debugging (debug), profiling (profile), release version(release), static release version (static) or code cover building (codecover)],
[case "${enableval}" in
  debug)   AC_CXXFLAGS+="-O0 -ggdb -D DEBUG " 		AC_LDFLAGS+="-ggdb " ;;
  profile) AC_CXXFLAGS+="-O3 -pg -ggdb -D NDEBUG " 	AC_LDFLAGS+="-ggdb " ;;
  release) AC_CXXFLAGS+="-O3 -D NDEBUG " 			AC_LDFLAGS+="" ;;
  static)  AC_CXXFLAGS+="-O3 -D NDEBUG " 			AC_LDFLAGS+="-static " ;;
  codecover) AC_CXXFLAGS+="-O0 -fprofile-arcs -ftest-coverage -ggdb -D DEBUG " AC_LDFLAGS+="-ggdb " ;;
  *) AC_MSG_ERROR([bad value ${enableval} for --enable-build]) ;;
esac],[		AC_CXXFLAGS+="-DNDEBUG $SD_CXXFLAGS -O3 " AC_LDFLAGS+="$SD_LDFLAGS "])

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
	32) AC_CXXFLAGS+=" -m32 " ;;
	64) AC_CXXFLAGS+=" -m64 ";;
	*) AC_MSG_ERROR([bad value ${enableval} for --enable-bits]) ;;
esac],[])

AC_ARG_ENABLE([gmp],
[  --enable-gmp    Turn on support for arbitrary size integer values],
[case "${enableval}" in
	no) AC_CXXFLAGS+=" -D NO_GMP " ;;
	yes) AC_CXXFLAGS+=" ";;
	*) AC_MSG_ERROR([bad value ${enableval} for --enable-gmp]) ;;
esac],[ AC_CXXFLAGS+=" -D NO_GMP " ])

# files to generate via autotools (.am or .in source files)
AC_CONFIG_FILES([Makefile tclap/Makefile])

# generate the final Makefile etc.
AC_OUTPUT
