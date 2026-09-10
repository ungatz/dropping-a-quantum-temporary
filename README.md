# Dropping a quantum temporary

When may a quantum compiler hand a temporary register back to the free pool,
and what does deciding that cost?

- `narrative/` — the paper and its supplement.
- `code/` — the checker (Haskell), the mechanised core (Lean), and the Silq
  programs of the comparison, with the transcripts Silq printed on them.

The paper is a working document. A blue rule and *In revision* marks prose
that is still being reworked; an amber rule and *Planned* marks a result that
belongs there and is not written yet. Skipping both leaves the finished
document.

## Building

Three separate builds, each from the repository root.

```
(cd narrative     && make)                          # build/full.pdf, build/supplement.pdf
(cd code/haskell  && cabal test)                    # the check suite
(cd code/lean     && lake exe cache get && lake build)
```

`make` writes into `narrative/build/`. The `full.pdf` and `supplement.pdf`
committed at `narrative/` are the built pair, copied up by hand.

MIT; see `LICENSE`.
