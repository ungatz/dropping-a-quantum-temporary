LATEXMK ?= latexmk
LUAFIGURES := abstract-criterion-lua abstract-dj-lua abstract-loan-lua abstract-matrices-lua abstract-program-a-lua abstract-program-b-lua abstract-program-c-lua abstract-records-lua abstract-reflection-lua abstract-witness-c-lua
FIGURE_PDFS := $(addprefix figures/,$(addsuffix .pdf,$(LUAFIGURES)))

.NOTPARALLEL:
.PHONY: abstract figures clean
abstract: $(FIGURE_PDFS)
	nice -n 19 $(LATEXMK) -lualatex -interaction=nonstopmode -halt-on-error abstract.tex

figures: $(FIGURE_PDFS)

figures/%-lua.pdf: figures/%-lua.tex figures/house-lua.tex
	cd figures && nice -n 19 $(LATEXMK) -lualatex -output-directory=. -lualatex='lualatex -interaction=nonstopmode -halt-on-error %O %S' $(notdir $<)

clean:
	$(LATEXMK) -C abstract.tex
	cd figures && $(LATEXMK) -C $(addsuffix .tex,$(LUAFIGURES))
