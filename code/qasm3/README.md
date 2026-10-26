# qasm3

Numerical checks of the OpenQASM 3 circuits the Haskell compiler emits, and the
reuse benchmark. The verdicts are exact in `../haskell/`; everything here is
numerical (tolerance 1e-9). Python 3.11 with `requirements.txt`.

```
pip install -r requirements.txt
(cd ../haskell && cabal test)      # writes the circuits into out-typed/
python3.11 compile_check.py
DQT_BIN="$(cd ../haskell && cabal list-bin exe:dqt)"
python3.11 reuse_check.py --dqt "$DQT_BIN" --programs ../haskell/programs
python3.11 allocation_check.py --dqt "$DQT_BIN" --programs ../haskell/programs
python3.11 emission_check.py --dqt "$DQT_BIN"
python3.11 wellformed_check.py
python3.11 -m unittest test_compile_check.py test_reuse_check.py
sh census-reproduce.sh
```

```
compile_check.py     every circuit in out-typed/, on every measurement branch,
                     against the machine's amplitude and the returned value
reuse_check.py       eleven fresh/reuse pairs compared as channels (REUSE.md)
allocation_check.py  pool admission, and a zero state at each released block
emission_check.py    gate emission against independently specified maps
wellformed_check.py  the checkers here refuse an ill-formed program by name
s_bench.py           the verdict at every drop and what three reuse schedules
                     cost, into s_bench_table.md
census.py            the paper's counts (26, 11, 14 + 1) from that table
engine.py            the language's machine, numerically
```
