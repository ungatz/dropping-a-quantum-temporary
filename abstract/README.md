# Abstract source

Compile with `make abstract` using `latexmk` and a TeX installation that provides `acmart`. The abstract uses the anonymous review class option.

`make figures` rebuilds the five editable standalone TikZ sources in `figures/` with pdfLaTeX. Their shared `figures/house.tex` requires TikZ/PGF, amsmath, Libertine (`libertine`), Inconsolata (`zi4`), and newtx math (`newtxmath`). The house file provides the palette and drawing styles.

The bundled implementation is an earlier snapshot. It does not yet include
the allocator's wire-reuse support described in this draft.
