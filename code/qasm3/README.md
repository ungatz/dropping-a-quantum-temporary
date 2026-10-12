# OpenQASM circuit comparison

This folder contains a numerical simulator for the OpenQASM 3 circuits emitted
by the Haskell compiler. It parses circuits with the reference `openqasm3`
parser, evaluates gates and measurement branches, compares final amplitudes
with the compiler suite's Haskell leaf data, and checks that output bits read
the returned qubits. The comparison uses a tolerance of `1e-9`; it is not
formal verification or hardware execution.

The probes vary the visible inputs; loans start in zero states. This does not
test every incoming loan state or entanglement with a caller. The simulator
also starts fresh qubits in zero states. OpenQASM declarations alone do not
provide that initialization; a device must satisfy the compiler's stated
[initial-state assumption](../haskell/README.md#compiler-assumptions-and-diagnostics).

Use Python 3.11. Install the pinned dependencies with
`python3.11 -m pip install -r requirements.txt`.

From `../haskell/`, generate the circuits and leaf data:

```sh
cabal test dqt-compile-test
```

Then, from this directory, compare them and run the parser-level negative
tests:

```sh
python3.11 compile_check.py
python3.11 -m unittest test_compile_check.py
```

The compiler writes files into `out-typed/` next to this script. They are
generated data and are not included in this source export.
