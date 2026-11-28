# 1RB1LC_1RC0LD_1LA0RB_1LB1LE_1RF0LA_---0RE

bbchallenge id 167198. One of the six-state holdouts whose halting from blank tape is open. **Lean proves that it
halts if and only if an explicit Collatz-like orbit reaches a remainder of zero** (`lean/Orbit.lean`, `halts_iff`,
kernel only); whether the orbit does is open, and heuristically it never does.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LC |
| B | 1RC | 0LD |
| C | 1LA | 0RB |
| D | 1LB | 1LE |
| E | 1RF | 0LA |
| F | --- | 0RE |

## What it does

Write `a` for the pair `10`. The run is a sequence of rounds. A round starts with the head in state D on the left end
of the tape `a 1^N` (blank on both sides); the first starts at N = 22, after 208 steps.

1. **Doublings.** From `D> a^K 1^m` with `m >= 2K+6` the machine zigzags between the block of pairs and the ones:
   the inner loop moves one pair from the left block to the right block and turns two 1s into a new pair
   (`L a^(x+1) 1 A> 0 0 a^y 1^(z+2)  ->  L a^x 1 A> 0 0 a^(y+2) 1^z`), and after `K` such zigzags and one last pass
   the head is back at the left end with `D> a^(2K+4) 1^(m-2K-6)`. Starting from K = 1, after j doublings
   K = 5·2^j − 4 and m_j = N + 10 − 10·2^j + 2j.
2. **Remainder.** The doublings stop at the first j with m_j < 10·2^j − 2. If m_j = 0, the head runs off the right
   end of `a^K` in state F onto a blank cell: **F0 halts**. Otherwise (m_j is even and at least 2) the 1s run out in
   the middle of a zigzag, the machine turns the configuration into `0 0 a^x 1^y`, then repeatedly turns two 1s into a
   pair while the tape grows by two cells on the left, and finally unfolds every pair into 1s:
   the next round starts at

       N' = 2K + 3m + 2 = 3N + 24 + 6j − 20·2^j.

N stays even, so m does too; 20·2^j lies between N and 2N, so N < N' < 2N. The visited tape grows by about N cells per
round on the right while the left end hardly moves (the "exp" side), and a round costs about N² steps (the "sqrt"
side).

| round | N | doublings j | pairs K | remainder m | step reached |
|---|---|---|---|---|---|
| 1 | 22 | 1 | 6 | 14 | 208 |
| 2 | 56 | 2 | 16 | 30 | 1,311 |
| 3 | 124 | 3 | 36 | 60 | 6,556 |
| 4 | 254 | 4 | 76 | 112 | 28,293 |
| 5 | 490 | 5 | 156 | 190 | 108,740 |
| 6 | 884 | 6 | 316 | 266 | 369,871 |
| 7 | 1,432 | 7 | 636 | 176 | 1,054,120 |
| 8 | 1,802 | 7 | 636 | 546 | 2,136,141 |
| 9 | 2,912 | 8 | 1,276 | 378 | 4,964,192 |
| 10 | 3,688 | 8 | 1,276 | 1,154 | 9,497,325 |
| 11 | 6,016 | 9 | 2,556 | 924 | 21,564,642 |

## The recursion in rule form

As the bbchallenge wiki writes Antihydra's: exact tapes, then rules with exact step counts. One family (the X of
`lean/Orbit.lean`), m even:

    X(K, m) := 0^∞ D> (10)^K 1^m 0^∞

    0^∞ A> 0^∞   --21-->                     X(1, 6)                  (then X(1, 22) at step 208)
    X(K, m)      --4K² + 22K + 26-->         X(2K + 4, m − 2K − 6)    m ≥ 2K + 6        (doubling)
    X(K, m)      --3m² + 4Km + 9m + 1-->     X(1, 2K + 3m + 2)        2 ≤ m < 2K + 6    (end of round)
    X(K, 0)      --2K + 3-->                 HALT                     (F reads 0)

Each target is the first X tape reached. The rules are `double`, `finish` and `halt_zero` of `lean/Orbit.lean`, chained
in `phase_spec` and `halts_iff`; X(1, 22) at step 208 is `blank_to_X22`. The step counts are proved for the tape moves
the rules are built from (`lean/Rules.lean`), but `lean/Orbit.lean` does not keep the totals; they are checked against
direct simulation (`py/steps.py`: 2,440 tapes including 40 halting X(K, 0), and every X tape of the first 10^8 steps of
the run), not stated in Lean. The bbchallenge wiki page of 1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE (the same table
started in state A) writes the recursion in pairs (a, b) = (K + 1, m/2 − 2). Example: X(1, 26) -> X(6, 18) -> X(16, 0)
-> halt takes 52 + 302 + 35 = 389 steps.

## Does it halt?

It halts exactly when some round has remainder m = 0, i.e. N = 10·2^j − 2j − 10 (N = 8, 26, 64, 142, 300, 618, …;
started at these values the machine does halt). This is a cryptid-type question:

- Lean (`lean/Orbit.lean`, kernel only): `halts_iff : HaltsFromBlank ↔ ∃ i, orbit i = none`, where `orbit` iterates
  `next N = phase 1 N` from 22 and `phase` is the doubling/remainder map above, written as a Lean function.
- The closed form is proved in Lean for every N (`lean/Closed.lean`, kernel only): with h_k = 5·2^k − k − 6 and
  N = 2n + 2, `next_closed` gives `next (2n + 2) = some (2(3n + 3k + 14 − 10·2^k) + 2)` for h_k < n < h_{k+1}, and
  `next_halt` gives `next (2 h_k + 2) = none` for k ≥ 1 (this is N ↦ 3N + 24 + 6k − 20·2^k, halting at
  N = 10·2^k − 2k − 10). The three holdouts 1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE, 1RB1LC_1RC0LD_1LA0RB_1LB1LE_1RF0LA_---0RE and 1RB1RE_1LC0RA_1RD0LB_1LB1RC_1LF0RD_---0LE iterate the same function f(n) = 3n − 10·2^k + 3k + 14 (h_k < n < h_{k+1}, halt at n = h_k), the second in the coordinate N = 2n + 2, from different starts (n = 4, 10, 1); the three orbits share no value in their first 20,000 steps (checked in Python). No congruence can prove that this orbit avoids the h_k: for every modulus dividing 2^16·3^9 no set of residue classes holds the orbit, is kept by the map and misses every h_k (kernel, `no_cong_10` and `no_cong_1` in [`1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE/lean/Congruence.lean`](../1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE/lean/Congruence.lean)). The same holds for **every** modulus M and every start: `no_cong_ever` in [`1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE/lean/CongAll.lean`](../1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE/lean/CongAll.lean) (kernel) proves that a property of the residues mod M that misses the h_k and is kept by the map from level K on holds at no value of any level ≥ K, so neither a congruence nor a 2-adic class can trap this orbit; adding the size of n inside its level at finite resolution does not help either (`py/trapsize.py` there).
- `c/check_map.c` runs the machine from `D> a 1^N` for every even N from 8 to 3000 and agrees with the closed form
  (including the halts).
- `py/orbit.py` iterates the map with exact integers: no halt in 10^6 rounds (see `status.json` for the closest
  approach of m to 0).
- Heuristic: along the orbit m looks like a uniform even number below 10·2^j (no residue class mod 3 … 64 is avoided),
  so round i halts with chance about 1/(5·2^j), and j grows by about 0.67 per round. A halt after the checked rounds
  has chance below 10^−200000 (after 10^6 rounds N has 666,845 bits; the closest approach of m to 0 was 3.8·10^−6 of its range, in round 736,098): probviously nonhalting, but a proof would need control of a Collatz-like
  orbit.

## Files

- `lean/Rules.lean`: nine one-pass rules for all values of their counts, generated by `py/gen_rules.py`
  (`bbtools.symtm`).
- `lean/Orbit.lean`: the zigzag and the transfer chained by induction, the doubling, the end of a round, the halting
  case, the map `phase`/`next`/`orbit`, the first 208 steps (`decide +kernel`) and `halts_iff`.
- `lean/Closed.lean`: the closed form of `next` (`next_closed`, `next_halt`).
- `py/orbit.py`: the map, iterated. `c/check_map.c`: the map against the machine.

## Status

Open, reduced to the orbit question above. Lean: `step_none_iff`, no halt in 10^7 steps (`lean/Blank.lean`) and the
reduction `halts_iff` (`lean/Orbit.lean`), and the closed form of the map (`lean/Closed.lean`). C (`tools/c/triage.c`): no halt in 10^9 steps.

## Pages

- [`pages/holdouts/1RB1LC_1RC0LD_1LA0RB_1LB1LE_1RF0LA_---0RE/explainer.html`](../../pages/holdouts/1RB1LC_1RC0LD_1LA0RB_1LB1LE_1RF0LA_---0RE/explainer.html)
- [`pages/holdouts/1RB1LC_1RC0LD_1LA0RB_1LB1LE_1RF0LA_---0RE/proof-status.html`](../../pages/holdouts/1RB1LC_1RC0LD_1LA0RB_1LB1LE_1RF0LA_---0RE/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1LC_1RC0LD_1LA0RB_1LB1LE_1RF0LA_---0RE/lean/check.sh
python3 holdouts/1RB1LC_1RC0LD_1LA0RB_1LB1LE_1RF0LA_---0RE/py/orbit.py 1000000
python3 holdouts/1RB1LC_1RC0LD_1LA0RB_1LB1LE_1RF0LA_---0RE/py/steps.py     # the rule table and its step counts against direct simulation
gcc -O2 -o check_map holdouts/1RB1LC_1RC0LD_1LA0RB_1LB1LE_1RF0LA_---0RE/c/check_map.c && ./check_map 8 3000 2
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE`](../1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE/README.md): rename A→C, B→A, C→B, D→D, E→E, F→F; it is this table started in state B
- [`1RB1RE_1LC0RA_1RD0LB_1LB1RC_1LF0RD_---0LE`](../1RB1RE_1LC0RA_1RD0LB_1LB1RC_1LF0RD_---0LE/README.md): rename A→D, B→B, C→C, D→A, E→E, F→F and exchange left and right; it is this table started in state D, in a mirror

<!-- end of related machines -->
