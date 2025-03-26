COQC = coqc
COQDEP = coqdep
COQDOC = coqdoc

MODULES  := ZtoConfl
TEX           := $(MODULES:%=latex/%.v.tex)

LIBNAME = Zprop
COQMKFILENAME=CoqZprop.mk

.PHONY: all coq clean doc pdf install force
.SUFFIXES: .v .vo .v.d .v.glob

all: coq

coq: src/$(COQMKFILENAME)
	@$(MAKE) -C src -f $(COQMKFILENAME)

%.mk : Makefile _%
	coq_makefile -f _$* -o $*.mk

src/$(COQMKFILENAME): Makefile
	cd src && { echo "-R . $(LIBNAME)" ; ls *.v ; } > _CoqProject && coq_makefile -f _CoqProject -o $(COQMKFILENAME)

install: all
	@$(MAKE) -C src -f $(COQMKFILENAME) install

clean:
	@if [ -f src/$(COQMKFILENAME) ]; then $(MAKE) -C src -f $(COQMKFILENAME) clean; fi
	rm -f src/$(COQMKFILENAME) src/_CoqProject

force:

$(TEX): force
	$(COQDOC) --gallina --interpolate --latex --body-only -s \
			$(patsubst %.v.tex,src/%.v,$(notdir $@)) -o $@

doc: latex/fmm2021.pdf $(TEX)

latex/fmm2021.pdf: latex/fmm2021.tex $(TEX)  latex/fmm2021.bib
	cd latex ; pdflatex fmm2021 ; pdflatex fmm2021 ; bibtex fmm2021 ; pdflatex fmm2021 ; pdflatex fmm2021

pdf:
	okular latex/fmm2021.pdf&

