# The paper

`full.tex` is the paper. Its theorem statements live in `statements.tex` and
its machinery in `preamble.tex`; `refs.bib` is the bibliography. Figures are
drawn standalone in `figures/` and included as PDFs, because tikz is not on
ACM's production list.

```
make            build/full.pdf
make figures    figures/*.tex -> PDF
```

The introduction and the section after it ask the question on three small
programs. The language comes next: syntax, statics, the five-rule machine,
type safety, and the compiler to OpenQASM 3. Then the criterion -- when a drop
is safe, and the single gate that reclaims the block -- and then measurement,
where the verdict is per record. The last four sections are the gate ring, the
price of deciding, the implementation and the related work. The proofs are
appendices A to D, after the bibliography.

An amber rule and *Planned* mark a result that belongs where it stands and is
not written yet. The block says which question it will answer; nothing inside
one is claimed.
