# Wire reuse demonstrations

Build the executable from `../haskell/` with `cabal build exe:dqt`. From this
folder, run:

```sh
DQT_BIN="$(cd ../haskell && cabal list-bin exe:dqt)"
python3.11 reuse_check.py --dqt "$DQT_BIN" --programs ../haskell/programs
python3.11 allocation_check.py --dqt "$DQT_BIN" --programs ../haskell/programs
python3.11 -m unittest test_reuse_check.py
```

`reuse_check.py` compares eleven fresh/reuse pairs and their independently specified
maps. Every input qubit, including every loan, is entangled with a reference.
The comparison keeps returned registers, loans and references, traces out the
other wires, and compares the unnormalized density matrix separately for every
measurement record at tolerance `1e-9`. This normalized Choi representation
determines each finite subchannel, including input-dependent record weights
(the Choi representation, equations 2.64-2.66 of "The Theory of Quantum Information",
Cambridge University Press, 2018);
the comparison itself is numerical. The reported Choi record weights are
probabilities for the maximally mixed input, not probabilities for every input.
Terminal output measurements are checked against the return tuple and removed
for this comparison so they cannot conceal lost coherence.

| Example | Fresh wires | Reused wires | What is checked |
|---|---:|---:|---|
| Program (a), then a second allocation | 3 | 2 | Visible identity beside the new register in one; restore before its X |
| Two phase-kickback temporaries | 3 | 2 | Visible identity; allocations at both zero and one |
| Explicit uncomputation of the same example | 3 | 2 | Same map and width with manual restoration |
| Two Grover iterations | 4 | 3 | The two-iteration Grover unitary |
| Two measured-AND temporaries | 4 | 3 | Identity with weight 1/4 on each of four records |
| Borrowed ancilla with an extra X | 5 | 5 | Three-controlled X and return of an arbitrary loan |
| Bell pair dropped jointly or separately | 3 | 3 | Same visible identity, different pool admission |
| Program (c), exposed prefix and witness | 2, 2, 3 | 2, 2, 3 | Both subchannels, including the safe kept-record witness |

Gate counts are calls written in the emitted body, with both arms of a
conditional counted and custom gate calls unexpanded. They include preparation
and restoration. They are not executed-path costs or a native-gate benchmark.
Fresh allocation and explicit uncomputation are the baselines here. Measurement
and reset may also permit reuse while preserving the reduced output channel;
these tests do not compare against a reset-based optimizer or claim that failure
of the unitary-restoration criterion rules out every form of reuse.

`allocation_check.py` checks the zero state immediately at each pool release,
before a later operation can hide an incorrect restoration. It also checks
reversed tuple order, splitting a restored block into later lifetimes, unreachable
records, unsafe and partially safe drops, loans, and unsupported restoration.
Deleting a release's restoring gate must make this check fail. The unit tests
also reject missing preparation, wrong output mappings, incomplete test data,
and invalid numerical comparisons.

The exact Haskell `dqt-demo-test` checks the local-gate decomposition against
all four columns of program (c)'s declared V, then compares the exposed prefix
with the witness on the kept record. It removes only the witness's fixed zero
ancilla. On normalized plus and minus inputs that record has probability one
and zero respectively. The numerical suite checks the emitted versions too.

These demonstrations cover basis allocations and a fixed return tuple. Loan returns
are compiled before the first lift or conditional. Record-dependent loan restoration,
an allocator with different wire maps on different records, and a proved numerical
error bound remain outside this implementation.
