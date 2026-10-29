# Abstract source

`abstract.pdf` is the LuaLaTeX rendering. Rebuild it with `make abstract` using `latexmk`, `acmart`, the Libertinus fonts and JetBrains Mono (Regular and SemiBold). The abstract uses the anonymous review class option.

`make figures` rebuilds the standalone TikZ `-lua` diagrams included by the abstract. Their text, mathematics and code use the same fonts as the document. These require TikZ/PGF, amsmath, fontspec and unicode-math. The house files provide the palette and drawing styles.

Language keywords use JetBrains Mono SemiBold; the other code uses Regular, with code ligatures disabled. Register names use the regular code face in the programs, prose and wire labels. Gates, states and semantic maps use the math face. Colours in nearby prose match the labelled branches or vectors in the figures.
