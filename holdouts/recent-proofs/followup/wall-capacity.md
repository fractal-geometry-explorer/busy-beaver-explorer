# wall-capacity: PR 97's "wall of capacity m" idea on two holdouts

Technique (PR 97, techniques/misc.md): skip the Collatz-like orbit. Prove only that one side of the tape is a "wall"
that takes every possible sequence of signals (bounces, or parities) and stays in a closed shape language with no
halt. For our two machines the long block's counter (N or z) sends one signal per step/phase: its parity (machine 1)
or its residue mod 4 (machine 2). The question is whether the wall survives **every** signal sequence. Any finite
sequence of residues can actually occur (the counter maps are affine with ratio 3/2, so a sequence of length j is
fixed by z mod 2^(j+O(1))).

The scripts are kept in the project's shared files, not in this repository.

## 1RB1RA_1LC0RB_1LD0LB_1RA0LE_---1LF_1LB0LA: the technique fails, because the halting branch is reachable

**Result: no residue-only invariant exists. Some step-start configuration of the run's own shape halts.**
Evidence level: computed (exact accelerated simulation). This does not decide the machine: the real orbit z = 11,
19, 31, ... is a different z.

- Adversarial search (`m2stats.py`, `m2chain.py`): phases run with a stand-in z of each residue (c/phase.c, the
  repo's method), starting from the run's real first prefix P = 1^14. A breadth-first search over prefixes of at
  most 80 cells, with both residues free at every phase, finds halting phases. (Up to 60 cells it finds none: 689
  prefixes.) The first chain found has 60 phases. Its residues and prefixes are in `m2chain_80.txt`. The last
  prefix is `1^5 0 1^10 0^3 1^6 0^3 1^6`. With z = 1 mod 4 the phase-end walk runs off the left end of P, and E
  reads a blank there, which is the halt. Checked cell by cell with phase.c for z = 241 ... 1005: it halts every time.
- An exact witness (`m2lift.py`): lifting the residues and bonuses gives z0 = 2082616591761832409 (mod 2^63).
  The configuration `1^14 0^z0 B>0`, the shape of the real phase 0, which there has z = 11, **halts after about
  4.398e57 steps**, in phase 59 (`m2lift_out.txt`). Each phase's residue matches the chain. The simulator
  `m2rle.py` is exact. It uses three rules:
  - run crossing;
  - the repo's Lean-proved sweep rule (`lean/Sweep.lean`), applied t times at once;
  - a new conversion cycle `1^4 C>0 1 -> 1^2 C>0 1^3` (8 steps). It is checked on a finite window that it never
    leaves (`m2cyc.py`), so it holds for every context.

  It agrees with phase.c (P', z' and step counts) on 400 random phases and on the halting phase (`m2val.py`).
- What this means: the stack P is not a wall of unlimited capacity. A deep carry (an inner zero block running out
  again and again) can reach the left end, and there the walk escapes in state E. A proof of non-halting must use
  real information about the z orbit: which residue sequences occur. That is a Collatz-type question (the README
  calls it "coin tosses"). PR 97's parity bookkeeping cannot replace it.
- Next: the Sweep and conversion rules plus `m2rle.py` give a fast exact phase engine. It could replace drive.py's
  stand-in heuristic and push the real orbit much further. A Coq/Lean proof of the halting witness is possible but
  decides nothing.

## 1RB1LF_1LC1RD_1RA1LA_0RA0RE_0RC---_1RF0LC: no halt under free parities, and no closed invariant found

**Result: open. The technique does not close with any abstraction I could build, and no halting branch was found
either.** Evidence level: computed with the repo's Lean-proved step map (`py/zonemap.py`, with N = 10^7 + parity or
10^9 + parity standing in for "N large").

- The free-parity game (parity of N chosen by an adversary, wall counts exact):
  - BFS (`m1adv.py 200 6`) from all 2,955 grammar walls `1 X_1..X_n` (n <= 3, k <= 6, open/closed items of
    py/stackmodel.py), walls up to 200 cells: 5,360 walls, 267 of them outside the stack grammar, no halt, never stuck.
  - BFS (`m1adv2.py 400 8 2`) from 343 grammar walls (n <= 2, k <= 8), walls up to 400 cells: 1,365 walls,
    154 of them outside the grammar, no halt, never stuck.
  - Random adversarial walks from `1` (`m1walk2.py`, 400 walks of up to 400 steps): 375 survive all 400 steps and
    25 exceed 600 cells (the longest wall has 846 cells). No halt.
  - Random walks from random grammar walls (300 walks of 30 steps): no halt.
  - The wall graph from `1` up to 700 cells (`zonemap.py graph 700`) did not finish within about 1.5 h, so it gives
    no result. The repo's 300-cell run gave 279 walls and no halt.
- Why the PR 97 abstraction does not close:
  1. Parities of the counts k inside the wall are not free: they follow from the exact counts. If they are made
     free (the parity-only abstraction), the stack model (`py/stackmodel.py`) breaks down. Counts go negative
     (`m1clos.py`: 28 cases in 200k ordered walls), and the order k_i <= k_(i+1) is not preserved (18k cases).
     A ratio invariant k_(i+1) >= a*k_i is not preserved for a = 2..5 (`m1clos2.py`): when a lower open counter
     grows, the ratio drops by about 1/3. Along exact orbits the reachable ratios are >= 5 (`m1ratio.py`), so the
     order is a property of the exact counts, not of parities.
  2. The model's "negative count" cases lead in the real step map to walls outside the stack grammar (runs 1^9,
     1^15, `b 01`, ...), not to halts. So the true closed language is larger than the stack grammar, and it has not
     been described. Arbitrary short walls can halt (5 of 4,000 random walls of <= 20 cells, e.g. `10101010010111`),
     so the language must exclude some patterns. The repo already tried n-gram and pushdown closures, without success.
- Unlike in machine 2, the bottom of this wall is safe: in the model a carry reaching the bottom creates a new
  item K(0) (`step([],1)`), and no escape was seen. So a parity-free invariant is still plausible here. It would need
  (a) the extended item grammar (open/closed counters plus the extra 1-run and `b01` items), (b) per-item
  response lemmas in Longitudinal style (each item is a segment that turns one parity signal into a signal for the
  item below plus an amount of b copies), and (c) an inequality between neighbouring counts, or a proof that the
  out-of-grammar walls come back into it. That is far more than PR 97's single block X. No Coq was written.
