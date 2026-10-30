# Build the abstract

Requires LuaLaTeX, `latexmk` and a LaTeX installation with `acmart`, `standalone`, TikZ/PGF, `fontspec` and `unicode-math`. The fonts are Libertinus (Serif, Sans, Math) and JetBrains Mono (Regular and SemiBold).

From the repository root:

```sh
cd abstract
make abstract
```

This builds the document and diagrams with LuaLaTeX and writes `abstract.pdf`, with five body pages plus references.

For a fresh rebuild in the same directory:

```sh
make -B LATEXMK='latexmk -g' abstract
```
