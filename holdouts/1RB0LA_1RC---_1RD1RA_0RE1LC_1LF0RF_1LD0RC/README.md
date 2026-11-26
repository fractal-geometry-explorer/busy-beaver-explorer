# 1RB0LA_1RC---_1RD1RA_0RE1LC_1LF0RF_1LD0RC

bbchallenge id 76289, group G08 (two-sided square-root growth). Whether it halts from blank tape is open.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LA |
| B | 1RC | --- |
| C | 1RD | 1RA |
| D | 0RE | 1LC |
| E | 1LF | 0RF |
| F | 1LD | 0RC |

## What it does

A two-sided bouncer whose head zig-zags across the tape. At the moments the head reaches a new cell on the right, the
tape read in the words `x = 0001`, `y = 0001111`, `z = 0111111` is

    1^3 x^2 z x^N (middle zone) (z x^2 y x)^K A>0

The zone right of the tail repeats exactly every 13 visits to the right end from the 112th on (through 3*10^8
steps, `c/edge.c`, `py/zones.py`); it feeds new periods into the tail, whose left end the middle zone eats into from
time to time. The run `x^N` grows more slowly and from time to time
freezes (at 185 after about 6*10^7 steps; a new run of x then grows to its right). The middle zone, a few dozen words
long, has no visible pattern. At the left end the same tape appears in a shifted code (words `0011`, `0000011`,
`0011111`); every sweep translates the whole tape between the two codes.

Shift rules (Lean, any n): `C> (0011)^n -> (1000)^n C>`, `A> (001)^n -> (111)^n A>`, `1^n A>1 -> A>1 0^n`,
`0 F> 0^n -> 0^n 0 F>`.

## How it would halt

The only halting transition is B1. B is entered only from A0 (`enter_B`), so it halts exactly at `A>0 1`. A is
entered from A1 (moving left; the cell to its right was just erased) and from C1 (moving right) (`enter_A`), so a halt
needs `C>1 0 1` (`halt_C`): C reads a 1 followed by an isolated 0. Isolated 0s are common (one in each z), but in
10^8 steps C has read 8.75 million 1s and always with `0 0` after them.

## What is established

- **Kernel** (`lean/Halt.lean`): `halt_B`, `halt_A`, `halt_C`, `enter_B`, `enter_A`.
- **Kernel** (`lean/Rules.lean`): `cconv`, `afill`, `aerase`, `fzero`.
- **Kernel** (`lean/RightPass.lean`): the left-to-right sweep as a transducer on the words X, Y, Z of the left code
  (8 crossings, `rule_sound`; any list without `Y` right before `Z`, `pass_sound`).
- **Kernel / native** (`lean/Blank.lean`): the halting configurations; no halt in 10^4 / 10^7 steps.
- **Trusted** (C): no halt in 10^11 steps (`c/longrun.c`); C reads 1s only in front of `0 0` in 10^8 steps
  (`c/trfreq.c`).
- **Trusted** (C + Python): the right end is periodic with period 13 visits (`py/zones.py`).
- **Heuristic**: the tape shape above (`tools/c/tmrun.c` records).
- **Failed**: window CTL (K <= 7), n-gram CPS (`tools/c/ngramcps.c`): plain at widths 4, 6, 8, and with LRU history (`-U`) or fixed history 2 and 4
  (`-H`) at widths 3 to 9, all UNKNOWN or over the configuration limit; also `-U` at width 10 and `-H 2` at width 10: UNKNOWN, `-U` at width 12: over the limit of 3*10^7 configurations.

## Open, and next steps

Open. A separation argument (prove the 13-visit cycle of the right end for all K and show that the halting
pattern can only come from there) does not work: in 10^9 steps every `C>1 0` away from the right edge happened at
the join between the run of x and the irregular middle (44 times, always followed by `0 0`; `c/evt.c`), and at the
right edge the next cell is blank. So the danger is next to the irregular middle. The macro map is now known (next section): the middle is the low end of a binary counter. Next: a closed
language over the words (digits left free, spacers of -1 allowed), checked in Lean through `TM.CTL.not_halts`.
whose digits are runs of x), and look for an invariant on the side of z that C approaches.

## The middle zone is a binary counter (26 November 2026)

Computed, not proved (`c/rounds.c`, `py/counter.py`, `c/flip.c`). Read the tape at each sweep (the first time the
head reaches the right end after a visit to the left end) as `111 s_0 d_1 s_1 d_2 ... d_m s_m`, where each `s_i` is a
run of spacers x = `0001` and each `d_i` is a digit, y = `0001111` for 1 and z = `0111111` for 0. The run x^N is just
the spacer s_1, and the "irregular middle" is the low end of a binary number whose high end is the tail (z x x y x)^K.

- **Right to left.** Each x, from the right end inward, sends one pulse to the right that adds 1 to the number formed
  by the digits on its right (nearest digit lowest); a carry past the last digit is lost. This is why the head
  turns at the positions of a ruler sequence when it crosses the run of x. The sweep sets N' = (N + S) mod 2^m, with
  N = Σ d_i 2^(i-1) and S = Σ s_i 2^i.
- **Left to right.** One pass in state C. Each block of adjacent 1-digits moves one spacer to the right, so s_i
  changes by d_(i+1) - d_i, and the right end appends `x y x`: S' = S - N' + 3·2^m, N' += 2^m, m' = m + 1.
- **The two together** make a = 3N - 2·2^m and b = 3S - 8·2^m rotate: (a, b) → (a + b, -a), of order 6. The tape
  is the binary expansion of (2/3)·2^m plus a small error that turns with period 6. That is the "period 13 visits"
  of the right end (13 visits of the end per 6 rounds).
- **Defect words are spacers of -1.** When a block of 1-digits has no x on its right, the machine overlaps two digits:
  `(1,3)(1,9)` = `0111 0111111111` stands for x y [-1] z, and `(3,7)` = `0001111111` for y [-1] y. With these values
  the rotation holds in 1,526 of the 2,025 consecutive pairs of sweeps of the first 2·10^10 steps. It breaks at
  rarer defect words (`(1,3)(1,3)(1,9)`, `(1,12)`, …), at sweeps where a second -1 meets a block of 1s and two digits
  merge (the digit count m drops, 120 times), and the error (a, b) then jumps to a larger orbit. So the error grows
  slowly, and with it the width of the irregular middle.
- **The danger is in the pulses.** A halt needs `C>1 0 1`. C reads a 1 followed by a 0 only where a pulse leaves the
  last unconverted x (`1000`) and meets the converted part, whose words all start with `00` (`0011`, `0000011`,
  `0011111` and the merged words). A word starting `01` there would halt the machine.
- **It does not depend on the digits.** `c/flip.c` runs the machine but flips every clean digit word (y ↔ z, the same
  7 cells) at random at every sweep, which destroys the arithmetic. 18 runs of 3·10^8 to 3·10^9 steps (650 to 860
  sweeps each, with flip probabilities 0.03, 0.5 and 1, both start states) never halt. So a proof should not need to
  know N: an invariant on the shape of the words should be enough.
- **The sibling** 1RB0LB_1RC0LD_0LA1RD_1LC1LE_1LF0RE_1LD--- (this table started in E, mirrored) has the same counter
  with the prefix `111 xxxxz` instead of `111 xxz` (`./rounds MACHINE STEPS 1 4`; the rotation holds 790 times in
  3·10^9 steps).
- **The wall-carry screen.** The screen of `holdouts/recent-proofs/recursive-sweeps-nov23-25.md` listed this table
  with values {0,3,6}, {1,4,7}, {2,5,8} by state behind the wall `2 2 2`. That signature is an artefact: the residue
  is fixed by the state of a head walking through a run of 1s, not a carry returned by a sweep. The carry here is a
  binary carry of any length, so the busycoq #115 core (three carry classes) does not apply.
- **Closed tape languages, first try.** Since the two codes use different run lengths (beyond 10 cells from the head,
  the left side has 0-runs of 1 or 3 and the right side 0-runs of 2, 3, 5, 6, 8, 11), we tried a language made of an
  exact window of K cells at the head plus run-length n-grams beyond it. It reaches no halting configuration, but
  for K = 6 to 10 and n = 2 to 5 it does not close yet: the far parts it allows let junk windows form near the tape
  ends.

## Files

| path | what it is |
|---|---|
| `lean/Machine.lean`, `lean/Blank.lean` | generated: the machine, its halting configurations, bounded runs from blank tape |
| `lean/Halt.lean` | how a halt comes about: the halting patterns and the ways into the halting state (kernel) |
| `lean/Rules.lean` | shift rules for any count (kernel, written by `tools/py/bbtools/symtm.py`) |
| `lean/RightPass.lean` | the left-to-right sweep over the words X, Y, Z, by induction on the word list (written by `py/gen_rightpass.py`) |
| `c/longrun.c` | the run from blank tape, with the tape's extent at powers of ten |
| `c/runhist.c` | the run lengths of the tape at every moment the head reaches a new cell |
| `c/trfreq.c` | how often each transition is used |
| `c/evt.c` | the tape around the head each time a given state reads a given symbol |
| `c/edge.c` | the whole tape each time the head reaches a fresh cell on one side |
| `py/zones.py` | cuts those tapes after the periodic tail and finds the period of the rest |
| `c/rounds.c` | the tape as words x, y, z at every sweep |
| `py/counter.py` | the tape of each sweep as the numbers N and S; checks the order-6 rotation |
| `c/flip.c` | the run with digit words flipped at random every sweep (no halt) |

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LA_1RC---_1RD1RA_0RE1LC_1LF0RF_1LD0RC/lean/check.sh
cd holdouts/1RB0LA_1RC---_1RD1RA_0RE1LC_1LF0RF_1LD0RC/c
gcc -O2 -o longrun longrun.c && ./longrun 1RB0LA_1RC---_1RD1RA_0RE1LC_1LF0RF_1LD0RC 100000000000      # about 20 minutes
gcc -O2 -o runhist runhist.c && ./runhist 1RB0LA_1RC---_1RD1RA_0RE1LC_1LF0RF_1LD0RC 10000000000
gcc -O2 -o trfreq trfreq.c && ./trfreq 1RB0LA_1RC---_1RD1RA_0RE1LC_1LF0RF_1LD0RC 100000000
gcc -O2 -o evt evt.c && ./evt 1RB0LA_1RC---_1RD1RA_0RE1LC_1LF0RF_1LD0RC 1000000000 C 1 6 3 | grep '\[1\]0'
gcc -O2 -o rounds rounds.c && ./rounds 1RB0LA_1RC---_1RD1RA_0RE1LC_1LF0RF_1LD0RC 20000000000 > r.txt && python3 ../py/counter.py r.txt
gcc -O2 -o flip flip.c && ./flip 1RB0LA_1RC---_1RD1RA_0RE1LC_1LF0RF_1LD0RC 3000000000 0.5 1
gcc -O2 -o edge edge.c && ./edge 1RB0LA_1RC---_1RD1RA_0RE1LC_1LF0RF_1LD0RC 300000000 R 1 > edgeR.txt && python3 ../py/zones.py edgeR.txt
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0LB_1RC0LD_0LA1RD_1LC1LE_1LF0RE_1LD---`](../1RB0LB_1RC0LD_0LA1RD_1LC1LE_1LF0RE_1LD---/README.md): rename A→E, B→F, C→D, D→C, E→A, F→B and exchange left and right; it is this table started in state E, in a mirror

<!-- end of related machines -->
