# Abstract source

Compile with `make abstract` using `latexmk` and LuaLaTeX, with `acmart` and the Libertinus fonts. The abstract uses the anonymous review class option. Programs are set in Iosevka Custom when it is installed and in Inconsolata otherwise.

`make figures` builds the figure PDFs from the standalone TikZ sources in `figures/`, and `make abstract` does so first for any figure that is out of date: the `-lua` copies with LuaLaTeX, so that their letters match the text, and the rest with pdfLaTeX. `figures/house.tex` requires TikZ/PGF, amsmath, Libertine (`libertine`), Inconsolata (`zi4`), and newtx math (`newtxmath`); `figures/house-lua.tex` requires TikZ/PGF, amsmath, `fontspec`, `unicode-math` and the Libertinus fonts. The house files provide the palette and drawing styles.
