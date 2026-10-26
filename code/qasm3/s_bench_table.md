| program | temporary | visible | verdict per record (weight) | measure+reset schedule | uncompute schedule (gates on t) | this paper, per shot | the verdict's price, once | reclaiming gate per record |
|---|---|---|---|---|---|---|---|---|
| a-then-u.s | t (d=2) | m=2 | -:SAFE(1) | 1 meas+reset | 1 gates | 0 | 1 pass(es), matrix 4x2 | -:reflection [[0.7071, 0.7071]; [0.7071, -0.7071]] |
| bell-block.s | t (d=4) | m=2 | -:SAFE(1) | 1 meas+reset | 1 gates | 0 | 1 pass(es), matrix 8x2 | -:reflection [[0.7071, 0, 0, 0.7071]; [0, 1, 0, 0]; [0, 0, 1, 0]; [0.7071, 0, 0, -0.7071]] |
| bell-pair-split.s | a (d=2) | m=2 | -:UNSAFE(1) | 1 meas+reset | 2 gates | 1 | 1 pass(es), matrix 8x2 | -:— |
| bell-pair-split.s | b (d=2) | m=2 | -:UNSAFE(1) | 1 meas+reset | 1 gates | 1 | 1 pass(es), matrix 4x2 | -:— |
| bell-pair.s | a,b (d=4) | m=2 | -:SAFE(1) | 1 meas+reset | 2 gates | 0 | 1 pass(es), matrix 8x2 | -:reflection [[0.7071, 0, 0, 0.7071]; [0, 1, 0, 0]; [0, 0, 1, 0]; [0.7071, 0, 0, -0.7071]] |
| c-decomposed.s | t (d=2) | m=2 | i:SAFE(0.5), o:UNSAFE(0.5) | 1 meas+reset | 14 gates | 1 | 2 pass(es), matrix 4x2 | i:I, o:— |
| c-exposed.s | no drop site | | | | | | | |
| c-witness.s | a (d=2) | m=2 | i:SAFE(0.5), o:SAFE(0.5) | 1 meas+reset | 1 gates | 0 | 2 pass(es), matrix 8x2 | i:I, o:X |
| c.s | t (d=2) | m=2 | i:SAFE(0.5), o:UNSAFE(0.5) | 1 meas+reset | 2 gates | 1 | 2 pass(es), matrix 4x2 | i:I, o:— |
| copy-input.s | x (d=2) | m=2 | -:UNSAFE(1) | 1 meas+reset | 1 gates | 1 | 1 pass(es), matrix 4x2 | -:— |
| dj.s | t (d=2) | m=2 | -:SAFE(1) | 1 meas+reset | 3 gates | 0 | 1 pass(es), matrix 4x2 | -:(Z-X)/sqrt2 |
| grover-two-rounds.s | t1 (d=2) | m=4 | -:SAFE(1) | 1 meas+reset | 3 gates | 0 | 1 pass(es), matrix 8x4 | -:I |
| grover-two-rounds.s | t2 (d=2) | m=4 | -:SAFE(1) | 1 meas+reset | 3 gates | 0 | 1 pass(es), matrix 8x4 | -:I |
| grover.s | t (d=2) | m=4 | -:SAFE(1) | 1 meas+reset | 3 gates | 0 | 1 pass(es), matrix 8x4 | -:I |
| learns-nothing.s | t (d=2) | m=2 | -:UNSAFE(1) | 1 meas+reset | 2 gates | 1 | 1 pass(es), matrix 8x2 | -:— |
| mcx-dirty-half.s | a (d=2) | m=16 | -:UNSAFE(1) | 1 meas+reset | 3 gates | 1 | 1 pass(es), matrix 32x16 | -:— |
| mcx-dirty-x.s | a (d=2) | m=16 | -:SAFE(1) | 1 meas+reset | 5 gates | 0 | 1 pass(es), matrix 32x16 | -:X |
| mcx-dirty.s | a (d=2) | m=16 | -:SAFE(1) | 1 meas+reset | 4 gates | 0 | 1 pass(es), matrix 32x16 | -:I |
| measured-and-twice.s | a (d=2) | m=4 | i:SAFE(0.5), o:SAFE(0.5) | 1 meas+reset | 2 gates | 0 | 2 pass(es), matrix 8x4 | i:X, o:I |
| measured-and-twice.s | b (d=2) | m=4 | ii:SAFE(0.25), io:SAFE(0.25), oi:SAFE(0.25), oo:SAFE(0.25) | 1 meas+reset | 2 gates | 0 | 4 pass(es), matrix 8x4 | ii:X, io:I, oi:X, oo:I |
| qpe.s | psi (d=2) | m=8 | -:SAFE(1) | 1 meas+reset | 4 gates | 0 | 1 pass(es), matrix 16x8 | -:X |
| rus.s | t (d=3) | m=3 | i:UNSAFE(0.889), o:SAFE(0.111) | 1 meas+reset | 3 gates | 1 | 2 pass(es), matrix 9x3 | i:—, o:swap |0>,|2> |
| shor.s | w (d=16) | m=8 | i:SAFE(0.25), o:UNSAFE(0.75) | 1 meas+reset | 4 gates | 1 | 2 pass(es), matrix 128x8 | i:swap |0>,|7>, o:— |
| simon.s | w (d=4) | m=4 | i:SAFE(0.5), o:SAFE(0.5) | 1 meas+reset | 1 gates | 0 | 2 pass(es), matrix 16x4 | i:I, o:swap |0>,|1> |
| superdense.s | a (d=2) | m=2 | ii:UNREACHABLE(0), io:UNREACHABLE(0), oi:SAFE(0.5), oo:SAFE(0.5) | 1 meas+reset | 6 gates | 0 | 2 pass(es), matrix 4x2 | ii:—, io:—, oi:X, oo:X |
| teleport.s | m (d=2) | m=2 | ii:SAFE(0.25), io:SAFE(0.25), oi:SAFE(0.25), oo:SAFE(0.25) | 1 meas+reset | 3 gates | 0 | 4 pass(es), matrix 8x2 | ii:I, io:I, oi:X, oo:X |
| teleport.s | a (d=2) | m=2 | ii:SAFE(0.25), io:SAFE(0.25), oi:SAFE(0.25), oo:SAFE(0.25) | 1 meas+reset | 3 gates | 0 | 4 pass(es), matrix 4x2 | ii:I, io:X, oi:I, oo:X |
| temp-and.s | a (d=2) | m=4 | i:SAFE(0.5), o:SAFE(0.5) | 1 meas+reset | 2 gates | 0 | 2 pass(es), matrix 8x4 | i:X, o:I |
| temp-general.s | a (d=2) | m=4 | i:SAFE(0.5), o:SAFE(0.5) | 1 meas+reset | 6 gates | 0 | 2 pass(es), matrix 8x4 | i:I, o:I |
| two-phases-uncompute.s | t (d=2) | m=2 | -:SAFE(1) | 1 meas+reset | 5 gates | 0 | 1 pass(es), matrix 4x2 | -:I |
| two-phases-uncompute.s | u (d=2) | m=2 | -:SAFE(1) | 1 meas+reset | 3 gates | 0 | 1 pass(es), matrix 4x2 | -:I |
| two-phases.s | t (d=2) | m=2 | -:SAFE(1) | 1 meas+reset | 3 gates | 0 | 1 pass(es), matrix 4x2 | -:(Z-X)/sqrt2 |
| two-phases.s | u (d=2) | m=2 | -:SAFE(1) | 1 meas+reset | 2 gates | 0 | 1 pass(es), matrix 4x2 | -:reflection [[0.7071, 0.7071]; [0.7071, -0.7071]] |
| C^3X, Elementary Gates, Lem. 7.2 (4 Toffolis, 1 dirty ancilla) | a1 (d=2) | m=16 | -:SAFE(1) | 1 meas+reset | 4 gates | 0 | 1 pass(es), matrix 32x16 | -:I |
| C^4X, Elementary Gates, Lem. 7.2 (8 Toffolis, 2 dirty ancillas) | a1 (d=2) | m=32 | -:SAFE(1) | 1 meas+reset | 6 gates | 0 | 1 pass(es), matrix 128x32 | -:I |
| C^4X, Elementary Gates, Lem. 7.2 (8 Toffolis, 2 dirty ancillas) | a2 (d=2) | m=32 | -:SAFE(1) | 1 meas+reset | 6 gates | 0 | 1 pass(es), matrix 64x32 | -:I |
| C^5X, Elementary Gates, Lem. 7.2 (12 Toffolis, 3 dirty ancillas) | a1 (d=2) | m=64 | -:SAFE(1) | 1 meas+reset | 6 gates | 0 | 1 pass(es), matrix 512x64 | -:I |
| C^5X, Elementary Gates, Lem. 7.2 (12 Toffolis, 3 dirty ancillas) | a2 (d=2) | m=64 | -:SAFE(1) | 1 meas+reset | 8 gates | 0 | 1 pass(es), matrix 256x64 | -:I |
| C^5X, Elementary Gates, Lem. 7.2 (12 Toffolis, 3 dirty ancillas) | a3 (d=2) | m=64 | -:SAFE(1) | 1 meas+reset | 6 gates | 0 | 1 pass(es), matrix 128x64 | -:I |
| Deutsch-Jozsa n=1, parity oracle | t (d=2) | m=2 | -:SAFE(1) | 1 meas+reset | 3 gates | 0 | 1 pass(es), matrix 4x2 | -:(Z-X)/sqrt2 |
| Deutsch-Jozsa n=2, parity oracle | t (d=2) | m=4 | -:SAFE(1) | 1 meas+reset | 4 gates | 0 | 1 pass(es), matrix 8x4 | -:(Z-X)/sqrt2 |
| Deutsch-Jozsa n=3, parity oracle | t (d=2) | m=8 | -:SAFE(1) | 1 meas+reset | 5 gates | 0 | 1 pass(es), matrix 16x8 | -:(Z-X)/sqrt2 |
| Deutsch-Jozsa n=4, parity oracle | t (d=2) | m=16 | -:SAFE(1) | 1 meas+reset | 6 gates | 0 | 1 pass(es), matrix 32x16 | -:(Z-X)/sqrt2 |
| Deutsch-Jozsa n=3, constant oracle | t (d=2) | m=8 | -:SAFE(1) | 1 meas+reset | 2 gates | 0 | 1 pass(es), matrix 16x8 | -:(Z-X)/sqrt2 |
| Grover mark n=2 | t (d=2) | m=4 | -:SAFE(1) | 1 meas+reset | 3 gates | 0 | 1 pass(es), matrix 8x4 | -:I |
| Grover mark n=3 | t (d=2) | m=8 | -:SAFE(1) | 1 meas+reset | 3 gates | 0 | 1 pass(es), matrix 16x8 | -:I |
| Grover mark n=4 | t (d=2) | m=16 | -:SAFE(1) | 1 meas+reset | 3 gates | 0 | 1 pass(es), matrix 32x16 | -:I |
| compute-copy-uncompute n=2 | s (d=2) | m=8 | -:SAFE(1) | 1 meas+reset | 3 gates | 0 | 1 pass(es), matrix 16x8 | -:I |
| compute-copy-uncompute n=3 | s (d=2) | m=16 | -:SAFE(1) | 1 meas+reset | 3 gates | 0 | 1 pass(es), matrix 32x16 | -:I |
| compute-copy-uncompute n=4 | s (d=2) | m=32 | -:SAFE(1) | 1 meas+reset | 3 gates | 0 | 1 pass(es), matrix 64x32 | -:I |
| measure-and-fix-up n=2 | a (d=2) | m=4 | i:SAFE(0.5), o:SAFE(0.5) | 1 meas+reset | 6 gates | 0 | 2 pass(es), matrix 8x4 | i:I, o:I |
| measure-and-fix-up n=3 | a (d=2) | m=8 | i:SAFE(0.5), o:SAFE(0.5) | 1 meas+reset | 6 gates | 0 | 2 pass(es), matrix 16x8 | i:I, o:I |
