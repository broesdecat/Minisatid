# Copyright 2007-2011 Katholieke Universiteit Leuven
# Use of this software is governed by the GNU LGPLv3.0 license
# Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
# Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium

EXTRA_DIST = inputformat.tex

inputformat.pdf: $(srcdir)/inputformat.tex
	pdflatex $(srcdir)/inputformat
	rm inputformat.nav -f
	rm inputformat.out -f
	rm inputformat.log -f