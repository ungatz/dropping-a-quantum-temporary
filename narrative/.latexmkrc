# latexmk configuration. Everything generated goes to build/.
#
# pdflatex + bibtex: acmart's ACM-Reference-Format.bst is a BibTeX style.
$pdf_mode = 1;
$bibtex_use = 2;          # run bibtex, and clean the .bbl
$pdflatex = 'pdflatex -file-line-error -halt-on-error -interaction=nonstopmode %O %S';
$max_repeat = 6;

# Keep the tree readable: everything latexmk generates goes in build/.
$out_dir = 'build';
$aux_dir = 'build';

# `make clean` removes these too, but latexmk -C should get them all.
$clean_ext = 'bbl blg fdb_latexmk fls run.xml synctex.gz';
