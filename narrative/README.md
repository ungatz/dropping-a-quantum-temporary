# The paper

`full.tex` is the paper; `supplement.tex` holds the proofs it defers, as a
separate PDF. Statements used by both live in `statements.tex`, so the two
cannot drift apart. `preamble.tex` holds the machinery.

```
make            full.pdf and supplement.pdf, in build/
make figures    figures/*.tex -> PDF
```

Sections 1--5 are programs with no measurement in them: the calculus, what a
drop is, exactly when it is safe, and what it costs to decide. Section 6 adds
measurement, where a measured outcome can be read back into the program.
Sections 7--9 -- where a verdict fixed before the run stops working, the
runtime check that repairs it, and several temporaries at once -- are outlines
in this draft rather than write-ups, and two subsections earlier are as well.
Sections 10--12 are the artifact, the related work, and what is open.

Three markers say what is settled, each a coloured rule down the left margin.
*In revision* means the prose is being reworked. *Planned* names a result that
belongs there and is not written yet, and says what question it will answer;
nothing inside such a block is claimed. *Outline* is a summary standing in for
a section, not an argument.

A `\cref` from the paper into the supplement does not resolve — say "the
supplement, Appendix A" instead. Figures are drawn standalone in `figures/`
and included as PDFs, because tikz is not on ACM's production list.
