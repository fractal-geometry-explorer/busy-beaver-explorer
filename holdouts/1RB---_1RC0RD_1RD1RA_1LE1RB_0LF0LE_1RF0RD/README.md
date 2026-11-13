# 1RB---_1RC0RD_1RD1RA_1LE1RB_0LF0LE_1RF0RD

bbchallenge id 140108. One of the six-state holdouts whose halting from blank tape is open (group G11, family
*separator counter*, shared with `1RB---_1LC1RE_0LD0LC_1RD0RB_1RF0RB_0LF1RA`).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | --- |
| B | 1RC | 0RD |
| C | 1RD | 1RA |
| D | 1LE | 1RB |
| E | 0LF | 0LE |
| F | 1RF | 0RD |

## What it does

**Events.** Every so often B reaches the right end of the tape on blank. At every such event the tape is blocks of
1s separated by single 0s, `1^x1 0 1^x2 0 ... 0 1^xr 0 1^N B>0`, with x1 >= 2 and a long last block N.

**Two binary counters (proved).** Right after an event the head, in state B, is at the left end of a binary
counter written in groups of three cells (`0 0 0` = digit 0, `0 0 1` = digit 1, lowest digit first), which reads
`0^d 1`. Left of the head is the bit string in pairs `1 b` (after the first two 1s), ending with the pair `0 1`
(the old separator and the first 1 of the old block). Call this configuration `P(d, bs)` (`P` in `lean/Count.lean`).
One *count*: B runs right over the trailing 1-digits (`0 0 1` -> `1 1 1`), writes `1 1 1` on the first 0-digit
and turns; E erases back to the pair `0 1`; then the carry of the left string is a leftward walk through a block of
1s (each cell shifted right, 3 steps a cell) up to the first 0, and D runs back rewriting `1 1` pairs as `1 0`. The
count adds 1 to the right counter and 4 to the left string (its two lowest pairs are scratch and come back unchanged).
2^d counts take the counter from `0^d 1` to `1^d 1`, and the next one carries into blank tape: the next event, one
digit more. So, with j = d + 1 = (N+2)/3,

> **event rule:** bits b (M of them), N  →  b + 2^j, N + 3, as long as the addition does not carry out of the top bit.

`lean/Count.lean` proves this for every size, every bit string and every left context (kernel): `count` (one count,
by cases on the lowest bit and the two carry lengths), `iter` (2^d counts, induction on d), `event_rule`
(`P d (b1 :: lo ++ h)` reaches `P (d+1) (b1 :: lo ++ inc h)` when `lo` has d bits and `h` contains a 0),
`event_to_P` (the event `bits 0 1^(3d+4) B>0` reaches `P (d+1) (bits + 2)`), `blank_to_P` (step 69 from blank is
`P 0 [0,1]`). Since these are runs, **the machine cannot halt between overflows** (a deduction from `blank_to_P` and `event_rule`, not itself a Lean theorem): it can halt only in a phase
whose addition carries out of the top bit. (Note: the bits at a P configuration are the bits of the event just
before it plus 2, because the first count of a phase finishes after the event.)

Example (steps 1,262,008 to 12,075,404): N = 43, 46, 49, 52, 55 and bit strings `0000110000010000101`,
`0001110000010000101`, `0011110000010000101`, `0111110000010000101`, `1111110000010000101` (2^15, 2^16, ... added).
`py/pchain.py` lists the P configurations of a run: to 2·10^7 steps, 22 phases follow `event_rule` and 6 are
overflows.

**Overflow.** When the addition carries out of the top bit, let R = X + 2^j - 2^M (X the bit string as a number).

- R even: the next event has X = R + 1 with M + 1 bits, N + 3 (the string grows by one bit).
- R odd: read R in pairs from the lowest bit; k = number of pairs at the bottom whose low bit is 1, r = R mod 4^k.
  The next event has X = C(r) + floor(R / 4^k), M + 3k + 1 bits, N - 3(2k - 1) (if that is -2: X halved, one bit
  fewer, N = 1). C(01) = 43, C(11) = 104, and for k >= 2, with t the number of trailing `11` pairs of r,
  C(r) = C(r >> 2) + c_t 8^(k-1), c_0 = 42, c_t = 248·4^(t-1) - 21 (2 c_(k-1) + 21 if all k pairs are `11`).

This map was read off runs of the machine. It agrees with every overflow of the run to 4·10^11 steps, with all
1,950 overflows of strings of at most 9 bits (run directly), and the recursion for C with all 126 patterns of k <= 6
and 12 random ones of k = 7, 8 (`py/macro.py`). The overflows of the run (bits, then M and j):

| step | before (M, j) | after (M, j) |
|---|---|---|
| 7,049 | `11100101` (8, 8) | `000000110001001` (15, 5) |
| 721,358 | `100000101101001` (15, 14) | `0000000000010000101` (19, 13) |
| 12,962,688 | `1111110000010000101` (19, 19) | `00000000000111111110000011` (26, 16) |
| 1,857,557,486 | `11111111110111111110000011` (26, 26) | `000000111111111110000001001000` (30, 25) |
| 48,364,000,185 | `111110111111111110000001001000` (30, 30) | `0111110111111111110000001001001` (31, 31), R even |
| 78,168,858,449 | `0111110111111111110000001001001` (31, 31) | `00000001111101111111111100000111101` (35, 30) |

**Halting.** The map covers every overflow except those whose odd pairs reach the top bit. Among those, for every
string of at most 9 bits, the machine halts only for the all-ones string with j = M: `1^(2M+2) 0 1^(3M-2) B>0`
(after 686, 1,390, 2,798 steps for M = 4, 5, 6; Lean, kernel); the other 67 such cases do not halt. So the machine
halts if and only if the map reaches a string whose odd pairs fill it (and then the all-ones one).

**The map iterated.** From the first event (step 39), 100,000 phases in 38 s: the odd pairs never reach the top; M
grows to 508,578 bits, about 10^153,000 machine steps. k at an overflow: 1 (35,315 phases), 2 (14,810), 3 (8,264),
4 (4,218), 5 (2,226), 6 (959), 7-10 (819), 11-20 (318), 21-92 (56); R even in 33,015. A halt needs k >= M/2.

**The shape of the string at an overflow (worker 2, round 2 of G11; computed with the trusted map).** In a phase
that starts with j = j0 the events add 2^j0, 2^(j0+1), ..., so the phase ends when the sum 2^j - 2^j0 passes 2^M.
After an overflow the new string is shorter than 2^j0, so the phase runs to j = M and the remainder is
R = X + 2^M - 2^j0: **the top M - j0 bits of R are all 1 and the low j0 bits are those of X**. This holds at 2,998
of the first 3,000 overflows (all but the 3rd and 5th). Call a pair of R (from the lowest bit) a *blocker* when its
low bit is 0: k is the place of the lowest blocker, and the halting case needs a string with no blocker. The shift
by 2k keeps pairs aligned, so blockers above the lowest one move down unchanged until the addition of C(r) (about
3k bits) reaches them. In 20,000 overflows of the map the number of blockers in R grows about linearly: 17 at
overflow 39 (M = 155), 639 at overflow 2,000 (M = 10,075), 3,302 at 10,000 (M = 50,724), 5,901 at 18,000
(M = 91,490), about one blocker gained per three overflows, and only 56 of the 20,000 overflows (all among the first
ones) have fewer than 20. So under the map a halt would need thousands of blockers to disappear at once; this is
evidence, not a proof: no invariant that keeps one blocker is proved, and the map itself is still trusted. The
recursive visit law that settled the corresponding point for the two-word sweepers
(`holdouts/1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RA_0LB---/lean/Stream.lean`) was not found here: in this machine every turn
of the head erases back into the left string, so a visit of the right side is not a function of the right side
alone.

**What non-halting reduces to.** Proved: the machine runs from blank to `P 0 [0,1]` and from each `P` to the next
whenever the addition stays inside the string. So it never halts if and only if every overflow phase ends in a new
`P` configuration. The overflow map above (trusted) says which one, and that the machine halts exactly when the map
reaches a string whose odd pairs fill it. Two things are open: (1) the overflow map for all sizes; (2) that the
iterated map never fills a string with odd pairs.

For (1): at an overflow the carry walks into the blank left of the string, the string is reset, and the head comes
back one cell out of phase with the counter (B reads the cell before a group, e.g. step 6,585:
`11.1.1.1.1.1.1.1.1.1 B> ..1.....1..1...........1`). In that phase the machine eats the counter's lowest digits two
at a time (k pairs, the counter loses 2k - 1 digits, the string gains 3k + 1 bits), which is where C(r) comes from.
Proving it means writing that phase as rules with variable lengths plus an induction on k, as `Count.lean` does for
the counts. For (2): the map behaves like a random process on growing strings; a halt needs k >= M/2 and the k seen
thin out geometrically (above). No invariant excluding the halting case is known; this looks like a Collatz-type
question, not something a finite certificate will settle.

## Status

Open. Lean: `lean/Blank.lean` (halting configurations; no halt in 10^7 steps), `lean/Rules.lean` (shift rules
`erase`, `fill`, `pairs`, `shift`, kernel), `lean/Shapes.lean` (`allones_4/5/6`: the halting pattern halts, kernel),
`lean/Count.lean` (the event rule for every size, kernel; halting only at an overflow follows from it and `blank_to_P`).
Trusted: the overflow map (`py/macro.py`), checked as above; no halt in 4·10^11 steps (`tools/c/tmrun.c`).
Heuristic: 100,000 phases of the map without a halt.

## Scripts

- `py/bitmodel.py events 1RB---_1RC0RD_1RD1RA_1LE1RB_0LF0LE_1RF0RD B LOG` checks every event of `tmrun 1RB---_1RC0RD_1RD1RA_1LE1RB_0LF0LE_1RF0RD T at B R 400 > LOG` against the rule;
  `py/bitmodel.py exhaust 1RB---_1RC0RD_1RD1RA_1LE1RB_0LF0LE_1RF0RD B 6` runs every 6-bit string and every j.
- `py/pchain.py MACHINE B 2e7` lists the post-event configurations `P d bs` of a run and checks each phase against
  `event_rule` (state E for the sibling).
- `py/accel.py MACHINE B N --c=PATH` (PATH: `gcc -O2 -o PATH c/transient.c`): the exact run, phase by phase with the
  proved rules (jumps whose endpoints are proved; step counts checked, not proved: steps of a count: 30 + 6t + 8r, summed in closed form; equal to the direct run at every P
  configuration to 2·10^7 steps) and the overflows simulated cell by cell. For this machine it reproduces the
  overflows of the table above (the seventh, P at step 1,857,557,588, after 3.7·10^8 simulated steps); the
  simulated stretch grows fast with k.
- `py/overflows.py MACHINE B MMAX`: every overflowing phase with at most MMAX bits, run to the next P configuration.
- `py/macro.py 100000` iterates the map; `py/macro.py 9 check LOG` compares it with the overflows of a log;
  `py/macro.py 0 checkO 9` runs every overflow of at most 9 bits; `py/macro.py 0 checkC 6` checks C.
- `py/blockers.py 20000`: the blockers at the overflows of the map (see above).
- `py/leanfiles.py` writes `lean/Rules.lean` and `lean/Shapes.lean` (shared by the batch; spec as JSON, see its
  docstring).

## Pages

- [`pages/holdouts/1RB---_1RC0RD_1RD1RA_1LE1RB_0LF0LE_1RF0RD/explainer.html`](../../pages/holdouts/1RB---_1RC0RD_1RD1RA_1LE1RB_0LF0LE_1RF0RD/explainer.html)
- [`pages/holdouts/1RB---_1RC0RD_1RD1RA_1LE1RB_0LF0LE_1RF0RD/proof-status.html`](../../pages/holdouts/1RB---_1RC0RD_1RD1RA_1LE1RB_0LF0LE_1RF0RD/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB---_1RC0RD_1RD1RA_1LE1RB_0LF0LE_1RF0RD/lean/check.sh
```
