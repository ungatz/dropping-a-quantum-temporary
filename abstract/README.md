# Abstract source

`abstract.pdf` is the LuaLaTeX rendering. Rebuild it with `make abstract` using `latexmk`, `acmart`, the Libertinus fonts and Iosevka Custom. The abstract uses the anonymous review class option.

`make figures` rebuilds the standalone TikZ diagrams. The abstract includes their `-lua` copies, whose text, mathematics and code use the same fonts as the document. These require TikZ/PGF, amsmath, fontspec and unicode-math. The unsuffixed pdfLaTeX copies use Libertine, Inconsolata and newtx math. The house files provide the palette and drawing styles.

Language keywords use a slightly heavier code face. Register names use the regular code face in the programs, prose and wire labels. Gates, states and semantic maps use the math face. Colours in nearby prose match the labelled branches or vectors in the figures.
