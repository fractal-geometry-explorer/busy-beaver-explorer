# 1RB0LE_1LC0RA_1LD0RC_1LE1LF_1LA0LC_0LA---

bbchallenge id 122192, a six-state holdout of group G05 (growth class fixed/sqrt). **Open.** The machine is an
exact macro machine on lists of numbers (a fuel counter, done blocks, a window with a dozen local rules). Lean
(kernel) proves one sweep for any list of done blocks and twelve window rules. The full macro machine has been
checked against the real run and runs 187,450 sweeps without meeting a case outside its rules.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LE |
| B | 1LC | 0RA |
| C | 1LD | 0RC |
| D | 1LE | 1LF |
| E | 1LA | 0LC |
| F | 0LA | --- |

## What it does

**The tape.** Look at the tape each time the head, in state A, is on the leftmost visited cell and reads a 1. Read
from the cell after the head, the tape is blocks of `10` separated by single cells. Write it as a list
`v0 s1 v1 s2 v2 ...`, where each v is a count of 10s and each separator is `.` (0) or `!` (1); blank tape is
`. 0 . 0 ...`. The first number `N = v0` is a **fuel** counter. Then come **done blocks** `w`, each followed by
the separator `sep = 0 1 1 0 0` (`. 0 ! 1 .` in the list). After them is the **window**, the first entry that is
not a done block. The right end of the tape is `... 1 ! 0`.

    cfg N ds W  =  A>1 (10)^N sep (10)^w1 sep ... (10)^wk sep W

**A sweep.**
- The head leaves the left end in state B (`start_s`, `start_z`).
- It crosses each done block in 2w + 21 steps (`rb`), leaving it as `(01)^(w-1) 1010101`.
- It does one local rule at the window and turns back in state A.
- On the way back it puts each block back, two cells further left (`lbA`/`lbD` for w ≥ 4, `lb3A`/`lb3D`,
  `lb2A`/`lb2D`). A 2-block hands the head on in state D, and the next block takes it back to A.
- At the left end the fuel has gone from N to N − 2 (`endA_s`, ...). With fuel 2 it ends at 0. With fuel 0 the
  list `0 sep v1 ...` becomes `2 . v1 ...`: the first done block joins the fuel. With fuel 1 one visit applies two
  rules; this is the one rare case.

**The window rules.** x is the value at the window:

| window | becomes | Lean |
|---|---|---|
| `x s y`, y ≥ 2 | `x+4 s̄ y−1` (separator flips) | `pair_dot`, `pair_bang` |
| `x ! 1 .`, `x ! 1 !` | `x+4 . 0 .`, `x+4 . 0 !` | `p1_bd`, `p1_bb` |
| `x . 1 !` | `x+4 ! 0 !` | `p1_db` |
| `x . 1 . z` | `x+5+z` | `p1_dd` |
| `x ! 0 ! z .` | `x+4+z .` | `merge` |
| `x . 0 . z` | x done, window `1 ! z` | `next` |
| `x . 0 . 0 . 0 ! 1 . v` | x done, window `2 ! 1 . v` | `restart2` |
| `x sep 1 ! 0` (end) | `x sep 2 sep 1 ! 0` | `append` |
| `x ! 0` (end) | `x+1` done, window `1 ! 0` | `end_b` |
| `x . 0 ! 0` (end) | `x+4 ! 0` | `end_db` |
| N's own `x s y` (no done blocks yet) | `x+2 s̄ y−1` | `own_dot`, `own_bang` |

`py/mac14.py` is this macro machine (`step`), with `fast` doing runs of pair rules and appends all at once.

**What emerges.** Each refill turns the leftmost done block into fuel. That fuel pays for runs of pair rules,
which multiply the window by about 4 while they count its neighbour down. Many of the resulting done blocks have
the form 4^k − 2 (2, 14, 62, 254, 1022, 4094, 16382). Long runs of 2-blocks pile up at the right end (10,748 of
them at sweep 74,633). Carries ripple through the middle of the list, a little like an odometer whose digits are
irregular.

## Status and evidence

**Lean, kernel only** (`lean/Rules.lean`, written by `py/gen_rules.py` with `bbtools.symtm.prove`): every cell
piece listed above, for all values of its counts and every surrounding tape. This covers 14 window lemmas and the
pair rule on the fuel block (`own_pair_dot`, `own_pair_bang`).

**Lean, kernel only** (`lean/Macro.lean`):
- the encoding `cfg`, `blk`, `blks` (done blocks nearest-first);
- `rpass` (right pass) and `lpass` (left pass), by induction over any list of done blocks with values ≥ 2. The
  left pass tracks whether the head is in state A or D (`pre`, `preA`, `preD`);
- `sweep_gen`: for fuel n+3, any done list and any window lemma that turns back in state A,
  `cfg (n+3) ds W` reaches `cfg (n+1) ds W'`. `sweep_gen2` (fuel 2 → 0) and `sweep_gen0` (fuel 0 → refill) are the
  same for the other fuel values;
- the window rules `pair_dot`, `pair_bang`, `append`, `p1_bd`, `p1_bb`, `p1_db`, `p1_dd`, `merge`, `end_db`,
  `next`, `end_b`, `restart2` (fuel ≥ 3);
- `own_dot` and `own_bang`, with exact step counts.

`lean/Axioms.lean` prints the axioms: only `propext` and `Quot.sound`.

**Computed (trusted):**
- `py/check.py 2e7` runs the machine 2·10^7 steps and compares every left-end visit (5,072 sweeps) with the list
  the macro machine predicted. It found no mismatch.
- `py/r14.c` prints the tape at every refill up to 10^10 steps. `py/cmp.py` finds the macro machine equal to the C
  run at all 33 refills (74,633 sweeps).
- `py/far.py` ran the macro machine 187,450 sweeps (600 s) without meeting a case outside its rules.

**Not proved:**
- the fuel-1 sweep;
- windows whose value is below the bound in the lemma (x ≥ 1, or x ≥ 4 for `next`, `end_b`, `restart2`,
  `append`);
- the rules other than pair on the fuel block;
- a single map on lists that puts all the rules together;
- and above all, an invariant that keeps the lists inside the rules forever.

Inside the proved rules the machine never reaches its halting move F1.

## Reproduce

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LE_1LC0RA_1LD0RC_1LE1LF_1LA0LC_0LA---/lean/check.sh
python3 holdouts/1RB0LE_1LC0RA_1LD0RC_1LE1LF_1LA0LC_0LA---/py/gen_rules.py     # rewrites lean/Rules.lean
python3 holdouts/1RB0LE_1LC0RA_1LD0RC_1LE1LF_1LA0LC_0LA---/py/check.py 2e7     # about 10 seconds
gcc -O2 -o r14 holdouts/1RB0LE_1LC0RA_1LD0RC_1LE1LF_1LA0LC_0LA---/py/r14.c && ./r14 1e10 100000 > r14.txt
python3 holdouts/1RB0LE_1LC0RA_1LD0RC_1LE1LF_1LA0LC_0LA---/py/cmp.py r14.txt
python3 holdouts/1RB0LE_1LC0RA_1LD0RC_1LE1LF_1LA0LC_0LA---/py/far.py 1e12 300 600
```

## Pages

- [`pages/holdouts/1RB0LE_1LC0RA_1LD0RC_1LE1LF_1LA0LC_0LA---/explainer.html`](../../pages/holdouts/1RB0LE_1LC0RA_1LD0RC_1LE1LF_1LA0LC_0LA---/explainer.html)
- [`pages/holdouts/1RB0LE_1LC0RA_1LD0RC_1LE1LF_1LA0LC_0LA---/proof-status.html`](../../pages/holdouts/1RB0LE_1LC0RA_1LD0RC_1LE1LF_1LA0LC_0LA---/proof-status.html)

## For later

Several days of work remain.

1. Finish the Lean macro machine:
   - the fuel-1 sweep (after `endA_s` with fuel 1 the head runs on into a second pass);
   - window lemmas for small x;
   - the other rules on the fuel block;
   - a function `next : List → Option List` with `next_sound`, as for holdout 1RB0LD_1LC1RD_….
2. Find an invariant on the lists: the shapes that appear at refills are very regular (4^k − 2 blocks, 2-block
   tails). The invariant must be closed under the rules and must exclude every window no rule covers. With it,
   non-halting follows as in the other macro-machine proofs.
3. Speed up `far.py`. After about 150,000 sweeps it slows down sharply because the pair runs get long. A
   closed form for a whole carry would let it go much further.

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0LE_1RC0LB_1RD1RF_1RE0RB_1LA0RD_0RE---`](../1RB0LE_1RC0LB_1RD1RF_1RE0RB_1LA0RD_0RE---/README.md): rename A→E, B→A, C→B, D→C, E→D, F→F and exchange left and right; it is this table started in state B, in a mirror
- [`1RB1RF_1RC0RE_1LD0RB_1RE0LC_1RA0LE_0RC---`](../1RB1RF_1RC0RE_1LD0RB_1RE0LC_1RA0LE_0RC---/README.md): rename A→C, B→D, C→E, D→A, E→B, F→F and exchange left and right; it is this table started in state D, in a mirror

<!-- end of related machines -->
