# Dropping a Quantum Temporary -- the paper and its supplement.
#
#   make            both PDFs
#   make figures    figures/*.tex -> PDF (drawn standalone; acmart never
#                   loads tikz, which is not on ACM's production list)
#   make clean      remove build products

LATEXMK := latexmk
COMMON  := preamble.tex statements.tex refs.bib
FIGSRC  := $(filter-out figures/house.tex, $(wildcard figures/*.tex))
FIGPDF  := $(FIGSRC:.tex=.pdf)

.PHONY: all figures clean distclean

all: build/full.pdf build/supplement.pdf

build/full.pdf: full.tex $(COMMON) $(FIGPDF)
	$(LATEXMK) -lualatex full.tex

build/supplement.pdf: supplement.tex $(COMMON) $(FIGPDF)
	$(LATEXMK) -lualatex supplement.tex

figures: $(FIGPDF)

figures/%.pdf: figures/%.tex figures/house.tex
	cd figures && $(LATEXMK) -lualatex -output-directory=. \
	    -lualatex='lualatex -interaction=nonstopmode -halt-on-error %O %S' $(notdir $<)

clean:
	-$(LATEXMK) -c full.tex supplement.tex
	rm -rf build

distclean: clean
	-$(LATEXMK) -C full.tex supplement.tex
	rm -rf build figures/*.pdf
