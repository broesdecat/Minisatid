# Copyright 2007-2011 Katholieke Universiteit Leuven
# Use of this software is governed by the GNU LGPLv3.0 license
# Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
# Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
AC_INIT([minisatid],[m4_esyscmd([./m4/version.m4])],[krr@cs.kuleuven.be])
AC_CONFIG_HEADERS([config.h])
AC_CONFIG_MACRO_DIR([m4])

#this is not an ideal solution, but it overrides the default cxxflags, so those set later are not invalid
if test -z $CXXFLAGS; then
    CXXFLAGS=" "
fi
AC_PROG_CXX
AC_PROG_LIBTOOL

AC_PROG_LEX
AC_PROG_YACC
AC_LANG([C++])

#found on http://realmike.org/blog/2010/07/18/gnu-automake-by-example/#doxygen
DX_HTML_FEATURE(ON)
DX_CHM_FEATURE(OFF)
DX_CHI_FEATURE(OFF)
DX_MAN_FEATURE(OFF)
DX_RTF_FEATURE(OFF)
DX_XML_FEATURE(OFF)
DX_PDF_FEATURE(OFF)
DX_PS_FEATURE(OFF)
DX_INIT_DOXYGEN(minisatid, doxygen.cfg, doc)

AM_INIT_AUTOMAKE([1.9 tar-pax foreign subdir-objects -Wall]) #silent-rules FROM VERSION 1.11 OTHER parameters like pedantic, seem no to work here, I set them in debug CXXflags!

#check for the necessary headers
AC_HEADER_STDC
AC_CHECK_HEADERS([\
	algorithm assert.h cassert cerrno cstdio cstdlib cstring ctime exception float.h \
	fstream gmpxx.h inttypes.h iomanip iostream limits limits.h list map queue \
	set setjmp.h signal.h sstream stack stdexcept stdint.h stdio.h stdlib.h string \
	tr1/memory tr1/unordered_map vector])
AC_TYPE_SIZE_T

# distribute additional compiler and linker flags
AC_SUBST([AC_CXXFLAGS])
AC_SUBST([AC_LDFLAGS])
AC_SUBST([LIBS])
AC_SUBST([MINISATID_VERSION])

MINISATID_VERSION=m4_esyscmd([./m4/version.m4 | tr -d '\n'])
AC_CXXFLAGS=" "
AC_LDFLAGS=" "

AC_CXXFLAGS+="-ffloat-store -Wall -Wextra -Wno-unused-parameter "
#should use -Wno-vla to allow variable sized arrays, which pbsolver has
#its too difficult too remove them there and only remaining issue with pedantic
#but our gcc doesnt support them yet

AC_ARG_ENABLE([build],
[  --enable-build    Turn on debugging (debug), profiling (profile), release version(release), static release version (static) or code cover building (codecover)],
[case "${enableval}" in
	debug)   AC_CXXFLAGS+="-O0 -ggdb -D DEBUG " 		AC_LDFLAGS+=" -ggdb " ;;
	profile) AC_CXXFLAGS+="-O3 -pg -ggdb -D NDEBUG " 	AC_LDFLAGS+=" -ggdb " ;;
	release) AC_CXXFLAGS+="-O3 -D NDEBUG " 				AC_LDFLAGS+=" " ;;
	static)  AC_CXXFLAGS+="-O3 -D NDEBUG " 				AC_LDFLAGS+=" -static " ;;
	codecover) AC_CXXFLAGS+="-O0 -fprofile-arcs -ftest-coverage -ggdb -D DEBUG " AC_LDFLAGS+="-ggdb " ;;
	*) AC_MSG_ERROR([bad value ${enableval} for --enable-build]) ;;
esac],[		AC_CXXFLAGS+="-O3 -D NDEBUG " 				AC_LDFLAGS+=" "])

AC_ARG_ENABLE([sat],
[  --enable-sat    Use minisat 2.0b(old), minisat 09z(hack) or minisat 2.2(new)],
[case "${enableval}" in
	old)   	oldm=true
			hackm=false
  		 	newm=false
  		 	;;
  	hack)  	oldm=false
			hackm=true
  			newm=false
  			;;
  	new)   	oldm=false
			hackm=false
  			newm=true
			;;
  	*) AC_MSG_ERROR([bad value ${enableval} for --enable-sat]) ;;
esac],[newm=true])

AM_CONDITIONAL([USEMINISAT],[test x$oldm = xtrue])
AM_CONDITIONAL([USEMINISAT09Z],[test x$hackm = xtrue])
AM_CONDITIONAL([USEMINISAT22],[test x$newm = xtrue])

AC_ARG_ENABLE([bits],
[  --enable-bits    Turn on 32/64 bit compiling],
[case "${enableval}" in
	32) AC_CXXFLAGS+=" -m32 " ;;
	64) AC_CXXFLAGS+=" -m64 " ;;
	*) AC_MSG_ERROR([bad value ${enableval} for --enable-bits]) ;;
esac],[])

AC_ARG_ENABLE([gmp],
[  --enable-gmp    Turn on support for arbitrary size integer values],
[case "${enableval}" in
	no) AC_CXXFLAGS+=" -D NO_GMP " ;;
	yes) AC_CXXFLAGS+=" -D GMP " LIBS+=" -lgmp -lgmpxx ";;
	*) AC_MSG_ERROR([bad value ${enableval} for --enable-gmp]) ;;
esac],[ AC_CXXFLAGS+=" -D NO_GMP " ])

AC_ARG_ENABLE([perftools],
[  --enable-perftools=false    Use the google perftools library for memory allocation (does not work for each OS, please consult "http://code.google.com/p/google-perftools/"],
[case "${enableval}" in
	no) perftools=false ;;
	yes) perftools=true ;;
	*) AC_MSG_ERROR([bad value ${enableval} for --enable-perftools]) ;;
esac],[ perftools=false ])

AM_CONDITIONAL([USEPERFTOOLS],[test x$perftools = xtrue])

AC_CONFIG_SUBDIRS([lib/tclap lib/perftools])
AC_CONFIG_FILES([Makefile doc/Makefile lib/Makefile lib/pbsolver/Makefile src/Makefile src/parser/Makefile src/minisatid-2.0.pc])

AC_OUTPUT
