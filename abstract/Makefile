LATEXMK ?= latexmk
FIGURES := abstract-loan abstract-matrices abstract-records abstract-reflection abstract-summed criterion
LUAFIGURES := abstract-loan-lua abstract-matrices-lua abstract-records-lua abstract-reflection-lua abstract-summed-lua criterion-lua
FIGURE_PDFS := $(addprefix figures/,$(addsuffix .pdf,$(FIGURES) $(LUAFIGURES)))

.PHONY: abstract figures clean
abstract: $(FIGURE_PDFS)
	$(LATEXMK) -lualatex -interaction=nonstopmode -halt-on-error abstract.tex

figures: $(FIGURE_PDFS)

figures/%-lua.pdf: figures/%-lua.tex figures/house-lua.tex
	cd figures && $(LATEXMK) -lualatex -output-directory=. -lualatex='lualatex -interaction=nonstopmode -halt-on-error %O %S' $(notdir $<)

figures/%.pdf: figures/%.tex figures/house.tex
	cd figures && $(LATEXMK) -pdf -output-directory=. -pdflatex='pdflatex -interaction=nonstopmode -halt-on-error %O %S' $(notdir $<)

clean:
	$(LATEXMK) -C abstract.tex
	cd figures && $(LATEXMK) -C $(addsuffix .tex,$(FIGURES) $(LUAFIGURES))
