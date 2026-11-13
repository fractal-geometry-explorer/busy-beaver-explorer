# 1RB0RE_1LC0RA_0LD1LB_1LA1LE_0LB0LF_1LD---

bbchallenge id 145615. A Collatz-like map on the number of 1s: S(3j) → S(10j+12), S(3j+1) → S(10j+14), S(3j+2) → S(10j−2) plus a remnant `0 (10)^6 1111`; with the remnants, the map is proved in Lean through 61,963 phases from blank tape (a halt would come after more than 2^6953 steps, kernel), then meets an unproved nested-remnant case.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RE |
| B | 1LC | 0RA |
| C | 0LD | 1LB |
| D | 1LA | 1LE |
| E | 0LB | 0LF |
| F | 1LD | --- |

## What it does

Phase start `S(m)`: the whole tape is `A> 1 1 1 0 1 0 1^m` (head in A at the left end). Inside a phase the tape is
`T(x, m) = 1 1 1 0 (10)^x 1^m`.

Proved in Lean (`lean/Rules.lean` from `py/rules.py`, `lean/Macro.lean` by hand):

| rule | from | to | steps |
|---|---|---|---|
| `round` | `T(x, m+3)` | `T(x+5, m)` | 6x + 51 |
| `zero` | `T(x, 0)` | `C> (11)^(x+6)` | 4x + 37 |
| `one` | `T(x, 1)` | `C> (11)^(x+7)` | 4x + 41 |
| `restart` | `C> 1 1 R` | `A> 1 1 1 0 1 0 R` | 16 |
| `start` | blank | `S(12)` | 75 |

so (`phase0`, `phase1`): **S(3j) → S(10j+12), S(3j+1) → S(10j+14)**, and (`reaches_S31957652`) the run from blank tape
goes S(12) → S(52) → S(184) → S(624) → S(2092) → S(6984) → S(23292) → S(77652) → S(258852) → S(862852) → S(2876184)
→ S(9587292) → S(31957652), the last at step 168,344,857,095,747 (`py/orbit.py`; the first ones agree with a direct
run). No halt before.

## Remnants (lean/Remnant.lean)

When m ≡ 2 (mod 3) two 1s are left after the rounds and the phase leaves a remnant `G(k, c) = 0 (10)^k 1^c`
right of the new ones. Phase starts in general are `P(m, W) = 0^inf A> 1 1 1 0 10 1^m G(k1,c1) G(k2,c2) ... 0^inf`.
After the rounds of the phase (x' = x + 5·⌊m/3⌋; all rules hold with any tape after them), proved with exact step
counts (`phase`, `phase_correct`):

| m mod 3 | next | rule |
|---|---|---|
| 0 | blank: P(2x'+10, []) | `zero` |
| 0 | G(k+1, c) W: P(2x'+11, G(k, c) W) | `zero_r` |
| 0 | G(0, c) W: P(2x'+10+c, W) | `zero_r` |
| 1 | blank: P(2x'+12, []) | `one` |
| 1 | G(k, c) W: the tape *is* T(x'+k+1, c) W (the remnant joins the phase) | `T_join` |
| 2, x' ≥ 8 | blank: P(2x'−4, [G(6, 4)]) | `two_b` |
| 2, x' ≥ 8 | G(k, c+3) W: P(2x', G(k+7, c) W) | `two_c` |
| 2, x' ≥ 8 | last G(k, 0) / G(k, 1): P(2x'−4, [G(6, 2k+4)]) / P(2x'−4, [G(6, 2k+6)]) | `two_0`, `two_1` |
| 2 | x' < 8, before G(k, 2), or before a non-final G(k, 0|1) | **not covered** |

So the m ≡ 2 case of a clean phase is `S(3j+2) → P(10j−2, [G(6, 4)])` for j ≥ 2 (`phase2_clean`).

From blank tape (`orbit_reaches`, `iter`): S(12) at step 75, ..., S(31957652) (phase 12), P(106525498, [G(6,4)])
(phase 13), S(355085028), ... The proved map covers **61,963 phases** (m then has 107,632 bits, the step 215,261
bits); every remnant list on the way has at most one block. Phase 61,964 is m ≡ 2 before `G(75, 2)`, not covered.
Hence (`halt_after`): if the machine halts, it runs more than **2^6953 steps** (`halt_time_kernel`, 2,000 phases
in the kernel) and more than **2^215260** (`halt_time_native`, all 61,963 phases, `native_decide`).
`py/remnant.py check 300` compares the map (phase starts and step counts) with direct runs; `orbit` iterates it.

## Halting

Only F1 halts; F is entered only from E1 (0LF): halts iff `1 E> 1`. None of the proved cases does it.

**Open case: m ≡ 2 before a remnant with c = 2** (the two leftover pairs meet). From T(10, 2) before G(k, 2):
k = 0 → P(26, [G(1,7)]), k = 1 → P(18, [G(9,1)]), k = 2 → a phase T(17, 4) with no remnant, k = 3 →
P(26, [G(0,2), G(4,4)]), k = 4 → P(16, [G(13,1)]): nested, with an outcome depending on k. Earlier direct runs
(`py/phase_m2.py`): S(14), S(17), S(23), S(26) take more than 3·10^7 steps.

- CTL K = 3..6: halts remain; n-gram CPS 3..7 fails.

## Notes for later

- Work out the case m ≡ 2 before G(k, 2) (and the small cases x' < 8): it looks like a phase run inside the
  remnant, a recursion on k. With it the map may cover the run much further, or a halt may appear.
- The sibling `1RB0RE_1LC0RA_0LD1LB_1LA1LF_0LB0RD_0LB---` shares states A, B, C and the (10)/(11) sweeps but behaves
  differently (a bouncer with a counter of separators).

## Pages

- [`pages/holdouts/1RB0RE_1LC0RA_0LD1LB_1LA1LE_0LB0LF_1LD---/explainer.html`](../../pages/holdouts/1RB0RE_1LC0RA_0LD1LB_1LA1LE_0LB0LF_1LD---/explainer.html)
- [`pages/holdouts/1RB0RE_1LC0RA_0LD1LB_1LA1LE_0LB0LF_1LD---/proof-status.html`](../../pages/holdouts/1RB0RE_1LC0RA_0LD1LB_1LA1LE_0LB0LF_1LD---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RE_1LC0RA_0LD1LB_1LA1LE_0LB0LF_1LD---/lean/check.sh
```
