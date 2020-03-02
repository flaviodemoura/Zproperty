MODULES  := ZProperty
VS            := $(MODULES:%=src/%.v)
TEX           := $(MODULES:%=latex/%.v.tex)
VS_DOC        := $(MODULES:%=%.v)

.PHONY: coq clean doc html pdf

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS)
	coq_makefile $(VS) \
		COQC = "coqc -R src Zproperty" \
		COQDEP = "coqdep -R src Zproperty" \
		-o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq .depend 
	cd latex; rm -f *.log *.aux *.dvi *.v.tex *.toc *.bbl *.blg *.idx *.ilg *.pdf *.ind *.out *.fls *.gz *.fdb_latexmk

doc: latex/Zproperty.pdf

COQDOC = coqdoc -R . Zproperty

latex/%.v.tex: Makefile src/%.v src/%.glob
	cd src ; $(COQDOC) --interpolate --latex --body-only -s \
		$*.v -o ../latex/$*.v.tex

latex/Zproperty.pdf: latex/Zproperty.tex $(TEX) latex/Zproperty.bib
	cd latex ; pdflatex Zproperty ; pdflatex Zproperty ; bibtex Zproperty ; pdflatex Zproperty ; pdflatex Zproperty

latex/%.pdf: latex/%.tex latex/Zproperty.bib
	cd latex ; pdflatex $* ; pdflatex $* ; bibtex $* ; makeindex $* ; pdflatex $* ; pdflatex $*

html: Makefile $(VS) src/toc.html
	mkdir -p html
	cd src ; $(COQDOC) --interpolate --no-externals $(VS_DOC) \
		-d ../html
	cp src/toc.html html/

PDF_OPEN = xdg-open latex/Zproperty.pdf&		

ifeq ($(OS),Windows_NT) # Se o Sistema Operacional for Windows...
else # Caso o Sistema Operacional seja Mac OS, modifica-se a variável pdf
UNAME_S := $(shell uname -s)
ifeq ($(UNAME_S), Darwin)
PDF_OPEN = open -a Skim latex/Zproperty.pdf&
endif
endif

# Assume-se o Linux como sistema operacional padrão
pdf:    doc
	$(PDF_OPEN)


