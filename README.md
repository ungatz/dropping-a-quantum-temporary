# Safe to Drop: an Exact Criterion for Quantum Temporaries

When may a quantum compiler drop a temporary register, and what does deciding
that cost?

- `narrative/` -- the paper and its figures.
- `code/` -- the checker and the compiler in Haskell, the OpenQASM 3 circuits
  it emits with the numeric check that re-simulates them, and the Silq
  programs of the comparison with the transcripts Silq printed on them.

## Building

```
(cd narrative    && make)        # build/full.pdf
(cd code/haskell && cabal test)  # the three suites
```

`make` writes into `narrative/build/`. The `full.pdf` committed at
`narrative/` is that build, copied up by hand.

An amber rule and *Planned* in the paper mark a result that belongs where it
stands and is not written yet; nothing inside such a block is claimed.

MIT; see `LICENSE`.
