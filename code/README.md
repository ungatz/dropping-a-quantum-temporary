# Safe to Drop: the artifact

When may a quantum temporary be dropped, and what does deciding it cost?
Three directories:

```
haskell/   the typed language with its checker, its five-rule machine, its
           elaboration and its compiler to OpenQASM 3; the drop criterion by
           two engines that check each other; and the suites that pin every number the
           paper prints
qasm3/     the emitted OpenQASM 3 circuits, the numeric checker that
           re-simulates them against the machine, and the reuse benchmark
silq/      the Silq programs of the comparison table, with the transcripts
           the Silq build printed on each of them
```

## The checker (`haskell/`)

```
cd haskell
cabal test                            # the three suites
cabal run dqt -- all                  # the whole report
cabal run dqt -- run programs/mcx-dirty.s
cabal run dqt -- typecheck programs/c.s
cabal run dqt -- compile programs/dj.s      # one program to OpenQASM 3
```

Everything also runs under `runghc -isrc` with no build. `haskell/README.md`
has the reading order, the table of every printed number and the function that
computes it, and the verdict of every example program.

## The compiler's output (`qasm3/`)

`cabal test` writes one `<name>.qasm` and one `<name>.leaves.json` per compiled
program into `qasm3/out-typed/`. Then, from `qasm3/`:

```
nice -n 19 python3 compile_check.py   # re-simulate each circuit against the machine
nice -n 19 python3 s_bench.py         # the reuse benchmark, into s_bench_table.md
```

`compile_check.py` needs `numpy` and the reference `openqasm3` parser;
`s_bench.py` needs `numpy`. `qasm3/README.md` says what each script does.

## The Silq comparison (`silq/`)

Reference material, not part of any build: the `.slq` programs, the driver
script `run_silq.sh`, and `TRANSCRIPT.md`, which records what Silq printed on
each program.
