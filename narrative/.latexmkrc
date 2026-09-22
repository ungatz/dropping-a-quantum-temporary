# Everything latexmk generates goes to build/.
$pdf_mode = 4;            # lualatex
$bibtex_use = 2;          # run bibtex, and clean the .bbl
$lualatex = 'lualatex -file-line-error -halt-on-error -interaction=nonstopmode %O %S';
$max_repeat = 6;

# preamble.tex and statements.tex are \input fragments, not documents: without
# this a bare `latexmk` in this directory tries to typeset them and fails.
@default_files = ('full.tex');

$out_dir = 'build';
$aux_dir = 'build';

$clean_ext = 'bbl blg fdb_latexmk fls run.xml synctex.gz';
