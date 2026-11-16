# 1RB0LD_0RC0RF_1LD0RB_1LE---_0LA0LB_0LE0RA

bbchallenge id 163738, group G08. Whether it halts from blank tape is **open**. Probable cryptid (see the class search below); proposed for family F12.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LD |
| B | 0RC | 0RF |
| C | 1LD | 0RB |
| D | 1LE | --- |
| E | 0LA | 0LB |
| F | 0LE | 0RA |

## What it does

A counter machine in disguise. At the left end the tape is a handful of long blocks of 1s, e.g.
`A> 000 1^3 00 1^x 00 1^7 000 1^y 0001000 1^z`. Going right, C packs every `1111` into `1000` (`pack`); going left, E
unpacks every `0001` back into `1111` (`unpack`). One round trip changes the counts by fixed amounts (here x − 8,
y − 8, z + 32; in other epochs x − 12, y − 4, z + 32, or x − 8, z + 24 with a fixed `(1000)^2` in front). When a
count runs out the blocks are rearranged and a new epoch starts with larger counts: the epochs of the first 6·10⁶
steps start with a block of 285, 851, 1,145 and 1,553 ones.

The machine halts only when D reads a 1; `1 A> 1` and `1 C> 0` halt at once, `1 1 E> 0` after two steps.

## Class search: one halting shape, reached on an exact line (13 November 2026)

Programs, not Lean: the engine with several free counts of `holdouts/1RB0LE_1RC---_0RD0RE_1LE0RB_0LA0LF_0RC0LD/py/closure/` (`paccel.py`,
`pclosure.py`, `pvalidate.py`, `hline.py`), and here `py/closure/yline.py`, `back.py` and the certificate
`classes_mod2.json.gz`. The tape is mirrored (the right end is the near end) and events are F at that end:

```sh
D=holdouts/1RB0LE_1RC---_0RD0RE_1LE0RB_0LA0LF_0RC0LD/py/closure ; E=holdouts/1RB0LD_0RC0RF_1LD0RB_1LE---_0LA0LB_0LE0RA/py/closure
export BBM=1RB0LD_0RC0RF_1LD0RB_1LE---_0LA0LB_0LE0RA BBEV=5 BBMIRROR=1 BBNODE='^00001101 \(1000\)\^n 101' BBMOD=2
python3 $D/pclosure.py bfs /tmp/c.json 5                    # the search, about 6 minutes; prints NOT CLOSED (one halt)
python3 $D/hline.py summary $E/classes_mod2.json.gz
python3 $D/pvalidate.py $E/classes_mod2.json.gz pieces && python3 $D/pvalidate.py $E/classes_mod2.json.gz points 3 2
python3 $E/yline.py plain ; python3 $E/yline.py run 90 ; python3 $E/back.py $E/classes_mod2.json.gz 2000
```

A node is the mirrored tape `F> 00001101 (1000)^P 101...` with P >= 20; a class is a node shape with every count of
at least 20 free, with its parity. Started from the first such node of the run from blank tape, the search **ends**:
7,030 classes, 8,015 pieces, none undecided, and exactly one piece halts,

    H(P)       =  F> 00001101 (1000)^P 101110110100001101                               P odd, P >= 21

Every other piece runs to a node of a class in the set, so (as far as the programs are right) **the machine halts
from blank tape if and only if its run visits H**. Checked against a plain simulator: 15,499 piece runs and 14,060
class points, 0 problems.

**How H is reached.** Searching backwards in the certificate (`back.py`) gives a ladder. In the shape

    Y(P, M, Q) =  F> 00001101 (1000)^P 1011 (1000)^M 1010100001 (1000)^Q 101000000101

and three more shapes of the same cycle, one turn of the cycle takes one block from M and three from Q, P stays
free, and the ladder ends in H exactly when **Q = 3M - 1** (with the matching offsets in the other three shapes).
Plain runs (`yline.py plain`): Y(21,3,8), Y(21,8,23), Y(23,8,23), Y(33,12,35), Y(21,22,65) halt (after 32,367 to
526,937 steps); with Q one or two off the line they do not halt in 3·10^6 steps. The backward search does not come
to an end (the ladder has a rung for every M, and tapes that enter the ladder from other shapes add more regions:
6,000 regions listed when stopped), so the complete set of tapes that lead to H is not written down.

**The run from blank tape (observed).** `yline.py run 90`: 103,758 nodes, up to a step count of 96 digits, no halt,
H never visited. Y is visited 972 times; the closest to the line is |Q - 3M + 1| = 101, and Q - 3M + 1 takes
every residue mod 2, 3 and 4, so no simple congruence keeps the run off the line.

This is the same picture as for the relative 1RB0LE_1RC---_0RD0RE_1LE0RB_0LA0LF_0RC0LD: a process on block counts
with one halting shape, entered when two counts hit an exact line. Halting is a Collatz-like question about one
orbit; the class method cannot decide it.

## Lean replay of the class search (16 November 2026)

`halts_iff` (`lean/Final.lean`), proved in Lean with `native_decide`:

    HaltsFromBlank ↔ ∃ P, P % 2 = 1 ∧ 21 ≤ P ∧ Reach init (H P)

where `H P` is the tape `101100001011011101 (0001)^P 1011000` (the rest blank) with the head in state F on the blank
cell right of it: the shape H above, seen without the mirror. So "halts if and only if the run visits H" is now a
Lean theorem, not only a result of the programs.

The mirror is proved first (`lean/Mirror.lean`, kernel only): this table is the table of
1RB0LE_1RC---_0RD0RE_1LE0RB_0LA0LF_0RC0LD with left and right exchanged and the states renamed (A, B, C, D, E, F here
are D, E, A, B, C, F there), a step commutes with the mirror image of the configuration, and so this machine halts
from blank tape if and only if that table halts from blank tape started in state D (`halts_iff_mirror`), and its run
reaches a configuration if and only if that run reaches the mirror image (`reach_iff_mirror`). `lean/MachineM.lean`
is that table started in D.

The rest is the replay of 1RB0LE_1RC---_0RD0RE_1LE0RB_0LA0LF_0RC0LD (see its README) applied to the mirror run:
`py/replay/explore.py` (start state D, nodes `F> 00001101 (1000)^n 101…`) writes the certificate
`py/replay/cert.json.gz`: 7,030 classes, 8,015 leaves, no cycle rules (shift rules only), one halting class (H with
P odd), and the arrival (4,800 executor moves from blank tape end at `F> 00001101 (1000)^21 10111010110100001`).
`py/replay/gen.py` re-checks it in Python (about 10 seconds) and writes the Lean data. `lean/Exec.lean`,
`Pieces.lean` and `Decode.lean` are copies (namespace changed, the arrival started in D); `Check0` … `Check7` and
`Arrive` evaluate the checks, `Replay.lean` gives `halts_iff_pre`, and `Final.lean` turns the one halting class into
H (`halts_iff_Hn`) and goes back through the mirror. Also proved: the run halts if and only if it reaches
`F> 00001101 (1000)^P 10101101000010100001101` (mirrored) for an odd P ≥ 21, the only start that runs into H
(`halts_iff_Xn`).

What it rests on: the mirror and the soundness theorems are checked by the kernel; the evaluations of the checks are
`native_decide`, so they also trust Lean's compiler (`#print axioms halts_iff`: `propext`, `Classical.choice`,
`Quot.sound` and the `native_decide` axioms of the checks). The whole check takes about a minute.

## What is proved, and where

- `lean/Blank.lean` (generated): the halting configurations; no halt in 10⁴ steps (kernel) and 10⁷ (`native_decide`).
- `lean/Rules.lean` (kernel, written by `py/rules.py`): `pack`, `unpack`, and the halting situations `halt_A`,
  `halt_C`, `halt_E`.
- `py/turns.py` (heuristic): the counters at every left turn (`python3 py/turns.py 1e7 | grep ' L  A> 000 '`).
- `lean/Mirror.lean` (kernel): the run is the mirror image of 1RB0LE_1RC---_0RD0RE_1LE0RB_0LA0LF_0RC0LD's table
  started in D (`halts_iff_mirror`, `reach_iff_mirror`).
- `lean/Final.lean` (`native_decide`, see above): `halts_iff`, halting if and only if the run reaches H.
- `c/visits.c` (trusted, our code): in the first 2·10⁸ steps the machine is in state D 26,324,186 times, always on a 0.

## What is open, next steps

The question itself. This is the most promising of the chaotic-looking part of the group: within an epoch the
counts move linearly, so each epoch's round trip is a symbolic rule that symtm can prove, and the epoch changes are
finitely many shapes. Next: list the epoch shapes, prove each round trip as a rule with the counts as variables, and
check that every epoch change leads to another listed shape (the same plan as for
`1RB0LF_1LC0LA_1RA0RD_---1RE_1LA1RC_0LB0RC`).

**Later**: not attempted beyond the first pass.

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LD_0RC0RF_1LD0RB_1LE---_0LA0LB_0LE0RA/lean/check.sh   # about a minute
R=holdouts/1RB0LD_0RC0RF_1LD0RB_1LE---_0LA0LB_0LE0RA/py/replay
python3 $R/explore.py /tmp/cert.json                    # the replay certificate, under a minute
python3 $R/gen.py --check                               # re-checks py/replay/cert.json.gz in Python, writes nothing
python3 holdouts/1RB0LD_0RC0RF_1LD0RB_1LE---_0LA0LB_0LE0RA/py/rules.py     # rewrites lean/Rules.lean
python3 holdouts/1RB0LD_0RC0RF_1LD0RB_1LE---_0LA0LB_0LE0RA/py/turns.py 1e7 | grep ' L  A> 000 '   # the counters at each left turn
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0LE_1RC---_0RD0RE_1LE0RB_0LA0LF_0RC0LD`](../1RB0LE_1RC---_0RD0RE_1LE0RB_0LA0LF_0RC0LD/README.md): rename A→D, B→E, C→A, D→B, E→C, F→F and exchange left and right; it is this table started in state C, in a mirror

<!-- end of related machines -->
