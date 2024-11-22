MODULES  := ZtoConfl
VS            := $(MODULES:%=src/%.v)
TEX           := $(MODULES:%=latex/%.v.tex)
VS_DOC        := $(MODULES:%=%.v)

.PHONY: coq clean doc html pdf

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS)
	coq_makefile $(VS) \
		COQC = "coqc -R src ZtoConfl" \
		COQDEP = "coqdep -R src ZtoConfl" \
		-o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq .depend 
	cd latex; rm -f *.log *.aux *.dvi *.v.tex *.toc *.bbl *.blg *.idx *.ilg *.pdf *.ind *.out *.fls *.gz *.fdb_latexmk

doc: latex/reportZtoConfl.pdf

COQDOC = coqdoc -R . ZtoConfl

latex/%.v.tex: Makefile src/%.v src/%.glob
	cd src ; $(COQDOC) --interpolate --latex --body-only -s \
		$*.v -o ../latex/$*.v.tex

latex/ZtoConfl.pdf: latex/reportZtoConfl.tex $(TEX) latex/zotLib.bib
	cd latex ; pdflatex reportZtoConfl ; pdflatex reportZtoConfl ; bibtex reportZtoConfl ; pdflatex reportZtoConfl ; pdflatex reportZtoConfl

latex/%.pdf: latex/%.tex
	cd latex ; pdflatex $* ; pdflatex $* ; bibtex --include-directory="/home/flaviomoura/workspace/org" $* ; makeindex $* ; pdflatex $* ; pdflatex $*

html: Makefile $(VS) src/toc.html
	mkdir -p html
	cd src ; $(COQDOC) --interpolate --no-externals $(VS_DOC) \
		-d ../html
	cp src/toc.html html/

PDF_OPEN = xdg-open latex/reportZtoConfl.pdf&		

ifeq ($(OS),Windows_NT) # Se o Sistema Operacional for Windows...
else # Caso o Sistema Operacional seja Mac OS, modifica-se a variável pdf
UNAME_S := $(shell uname -s)
ifeq ($(UNAME_S), Darwin)
PDF_OPEN = open -a Skim latex/reportZtoConfl.pdf&
endif
endif

# Assume-se o Linux como sistema operacional padrão
pdf:    doc
	$(PDF_OPEN)


