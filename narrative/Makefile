# Safe to Drop -- the paper.
#
#   make            build/full.pdf
#   make figures    figures/*.tex -> PDF (drawn standalone; acmart never
#                   loads tikz, which is not on ACM's production list)
#   make clean      remove build products

LATEXMK := latexmk
COMMON  := preamble.tex statements.tex refs.bib
# house.tex is an \input fragment shared by every figure, not a document of
# its own -- without this filter make tries to compile it and fails.
FIGSRC  := $(filter-out figures/house.tex, $(wildcard figures/*.tex))
FIGPDF  := $(FIGSRC:.tex=.pdf)
# Quoted source artwork, not a generated TikZ product.
FIGASSET := figures/barenco-original.pdf

.PHONY: all figures clean distclean

all: build/full.pdf

build/full.pdf: full.tex $(COMMON) $(FIGPDF) $(FIGASSET)
	$(LATEXMK) full.tex

figures: $(FIGPDF)

figures/%.pdf: figures/%.tex figures/house.tex
	cd figures && $(LATEXMK) -lualatex -output-directory=. \
	    -lualatex='lualatex -interaction=nonstopmode -halt-on-error %O %S' $(notdir $<)

clean:
	-$(LATEXMK) -c full.tex
	rm -rf build

distclean: clean
	-$(LATEXMK) -C full.tex
	rm -rf build $(FIGPDF)
