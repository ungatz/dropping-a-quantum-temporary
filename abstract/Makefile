LATEXMK ?= latexmk
FIGURES := abstract-loan abstract-matrices abstract-records abstract-reflection criterion
FIGURE_PDFS := $(addprefix figures/,$(addsuffix .pdf,$(FIGURES)))

.PHONY: abstract figures clean
abstract: $(FIGURE_PDFS)
	$(LATEXMK) -pdf -interaction=nonstopmode -halt-on-error abstract.tex

figures: $(FIGURE_PDFS)

figures/%.pdf: figures/%.tex figures/house.tex
	cd figures && $(LATEXMK) -pdf -output-directory=. -pdflatex='pdflatex -interaction=nonstopmode -halt-on-error %O %S' $(notdir $<)

clean:
	$(LATEXMK) -C abstract.tex
	cd figures && $(LATEXMK) -C $(addsuffix .tex,$(FIGURES))
