# 1RB1RF_1RC0RE_1LD0RB_1RE0LC_1RA0LE_0RC---

bbchallenge id 75404. One of the six-state holdouts whose halting from blank tape is open. Group G07 (fixed/sqrt
growth), family **block queue with cursors (counter-like), block sizes 4^j - 2**. Like
1RB1RF_0RC0RE_0RD1RA_1LE0LA_1LB0LD_0RD--- (a different machine with the same kind of run), its tape is a queue of
blocks (01)^k that cursors travel through. The local rules are proved in Lean; the form of the tape that the run
keeps does **not** by itself exclude a halt (a tape of that form that halts is proved in Lean). An exact accelerated
simulator (`go/fsim.go`) runs it to 10^5000 steps without a halt; in that run the halting shape came within one
coincidence nine times, each time missed by a margin of about the square root of the step count. Halting is open;
heuristically it does not halt.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RF |
| B | 1RC | 0RE |
| C | 1LD | 0RB |
| D | 1RE | 0LC |
| E | 1RA | 0LE |
| F | 0RC | --- |


## Status

**Open.** No closed invariant was found, and the natural one fails: see "The case that escapes". What is
established:

* the local rules of the queue for all parameters (Lean, kernel): feeding, crossing a separator, birth of a cursor;
* a tape of the block form that halts (Lean, kernel): the invariant "blocks, separators and cursors" is not enough;
* no halt in the first 10^18 steps (`py/qsim.py`) and in the first **10^5000** steps (`go/fsim.go`, 29 minutes);
  both are exact simulators of the table with accelerations that are validated against plain simulation, the
  periodic jumps are not proved;
* in those steps the dangerous shape (three cursor cells 1 side by side) stood on the tape at nine of the visits of
  the right end that the simulator stopped at (the first at step 1.057x10^11); each time it would have had to coincide with a birth to be left
  standing, and each time the end block still held about 10^(d/2) copies, d the number of digits of the step count.

## What it does

Write `a` for `01` and `b` for `00110`. At the moments the head, in state B, steps onto a new cell at the right end
(a *visit*), the tape is

    1 a  (blocks a^k separated by b, with single cursor cells in between)  a^M 0 B> 0^inf

A *cursor* is a single cell 0 or 1 that stands where the alternation `0101..` is broken (b itself is `0 a 1 0`:
two such cells with one a between them). The rightmost cursor is the *active* one. One visit of the right end does
this (all proved for all sizes, `lean/Rules.lean`):

* **feeding**: the active cursor moves one a to the left and flips; the block right of it gets 4 copies of a, the
  block at the end loses 2 (`feedb0`, `feedb1`); when no separator is right of the cursor the end block is the
  block right of it and gets 2 (`feed0`, `feed1`):

      L a^(k+1) 0 a^m b a^(n+2) 0 B>  ->  L a^k 1 a^(m+4) b a^n 0 B>       4m+4n+52 steps
      L a^(k+1) 0 a^m 0 B>            ->  L a^k 1 a^(m+2) 0 B>             4m+18 steps

  So a cursor that walks through a block of k copies leaves 4k behind it (2k without a separator), which is where
  the sizes 2, 14, 62, 254, ... (each 4k + 6, that is 4^j - 2) come from.
* **crossing a separator**, two visits: `b 0 a^m` -> `0 a 1 1 a b a^m` -> `0 a^6 b a^m` (`hop0a`, `hop0b`: the
  separator moves 6 copies to the right, the cursor is across), and `b 1 a^m` -> `0 0 a^(m+5)` -> `1 a b a^m`
  (`hop1a`, `hop1b`).
* **birth**: when the end block is used up (`... b 0 B>`), the last separator becomes a new cursor:
  `L a^(k+1) c a^m b 0 B>` -> `L a^k c' a^(m+4) 0 a 1 B>` -> `... 0 a^2 0 B>` (`birth0`, `birth1`, `birth2`).
  From then on the new cursor is the active one and the old cursor **stays where it is**.
* Cursors that come to stand side by side (observed on small tapes, `py/escape.py START 3,304,842`; not in Lean):
  `1 1` disappears (becomes a), `0 0` becomes `1 a b`, `1 0` becomes `0 a^3 b`. With no cursor at all, a visit
  inserts a block `b a^2` at the far left, after the leading `1 a` (the end block pays for it).

Long-lived cursors sweep the whole queue and turn every block k into 4k + 6, while the numbers of equal blocks
persist from one size to the next: at 2x10^15 steps the tape holds `(b a^254)^1264 ... (b a^1022)^127 ...
(b a^16382)^258`, at 10^18 steps `(b a^16382)^1264 ... (b a^65534)^127 ... (b a^1048574)^258` (the same three counts,
three sizes up), a self-similar counter. The
head's round trips cross the whole tape, so the right end grows like the square root of the step count.

## Where it could halt, and the case that escapes

The machine halts only on F reading 1, and F is entered from A reading 1 (A moves right): a halt needs A to read a
1 followed by another 1. In the block form this happens in one situation: **three cursor cells 1 side by side with
the next cursor, a 0, arriving directly right of them** (`... a 1 1 1 0 a^m 0 B>`; four 1s in a row on the tape).
`lean/Escape.lean` proves that the tape

    0^inf 1 a b a 0 a 1 1 1 0 a^22 0 B> 0^inf

halts after 213 steps (kernel). So "blocks, separators and cursors" is not a closed invariant that excludes halting;
with block sizes left free the form reaches a halt. The way to this tape (`python3 py/escape.py`, 14 visits):

    1 a b a 0 a 1 1 a b 0 b a 0 B>      a cursor 0 was left half way across a separator (0 a 1 1 a b, the middle of
                                         hop0a/hop0b) and a second cursor stands right of it
    1 a b a 0 a 1 1 a 0 a^6 b 0 B>      the second cursor arrives next to the pair; the end block is empty
    1 a b a 0 a 1 1 1 a^10 0 a 1 B>     a birth at exactly this visit: the three 1s are left standing
    ...                                  the new cursor walks left through a^10
    1 a b a 0 a 1 1 1 0 a^22 0 B>       it arrives as a 0: halt

Three things have to happen: (1) a birth while a cursor is half way across a separator, which leaves
`0 a 1 1 a b`; (2) a later cursor reaching that place; this gives `1 1 1` for one visit and `0 a 1 a^14` at the
next; (3) a birth at exactly that one visit, so that `1 1 1` is left standing, and the new cursor arriving as a 0.

**How often in the run from blank tape** (`python3 py/births.py 1e18`, accelerated simulator):

* births: 124 in the first 10^18 steps (22 by 7x10^8 steps, 119 by 10^17). The cursor left behind
  stands inside a block 86 times, directly after a separator 24 times, there is none 13 times, and it is
  **half way across a separator once** (birth 22, step 7.08x10^8): step (1) happened once.
* step (2) followed at step 1.057x10^11: the tape read `... b a^14 0 a 1 1 1 a^10 (b a^254)^258 ... b a^14076 0 B>`.
  This is the only visit, among the 3,304,842 simulated one by one, with three cursor cells 1 side by side.
* step (3) did not happen: the end block held 14076 copies at that visit, not 0, and one visit later the place read
  `0 a 1 a^14`.

**To 10^5000 steps** (`go/fsim.go 5000 quiet`, 29 minutes, 43,426,874 visits stopped at, of them 37,720,920 simulated
one by one, 12,527,123 bulk feedings, 12,064 periodic jumps, no rollback): no halt. 51,981 births were seen at the
visits simulated one by one, 74 of them with a cursor left half way across a separator (step (1)), and step (2)
happened nine times. At each of the nine visits the active cursor was the third 1 of the triple and the end block
`b a^M 0` was far from empty; a birth at that visit needs the end block to be used up there, so the next birth was at
least M/2 visits away:

| triple | step count | digits of M | M mod 8 | visits to the next birth, at least |
|---|---|---|---|---|
| 1 | 1.057x10^11 | 5 | 4 | 7,038 |
| 2 | ~10^394 | 197 | 2 | 2.28x10^196 |
| 3 | ~10^1735 | 867 | 0 | 5.67x10^865 |
| 4 | ~10^2720 | 1359 | 2 | 1.08x10^1358 |
| 5 | ~10^3274 | 1636 | 4 | 4.23x10^1635 |
| 6 | ~10^3533 | 1766 | 0 | 1.43x10^1765 |
| 7 | ~10^3570 | 1784 | 0 | 2.37x10^1783 |
| 8 | ~10^3723 | 1860 | 6 | 4.50x10^1859 |
| 9 | ~10^4994 | 2496 | 0 | 1.23x10^2495 |

(M mod 8 takes several values, so no simple congruence keeps the end block from running out at such a visit.)

**Heuristic.** Count the chances: a triple needs a birth exactly at its visit, while the active cursor's end block
holds M copies, M of the order of the square root of the step count (the length of the tape). If the visit at which
the end block runs out fell at random within the cursor's life, a triple would end in a halt with probability about
2/M: about 1/7000 for the first one, below 10^-196 for every later one. Triples come about once in 550 decades of
the step count (9 in 5000), so the chance that any later triple ends in a halt is below 10^-2490. On this model the
machine does not halt. This is an estimate, not a proof: the end block's size at a triple is determined, not random,
and an exact statement needs the global schedule of the cursors, which is not understood. The sibling
1RB1RF_0RC0RE_0RD1RA_1LE0LA_1LB0LD_0RD--- has an outside proof in review that it halts; its folder here does not
contain that proof, so its mechanism could not be compared; a halt by a structured coincidence that the random model
misses cannot be ruled out.

Closed-tape-language searches do not close: `tools/c/ngramcps.c` up to width 16 (and 20 to 36 with 4 or 6 bits of
history) ends UNKNOWN or at its limit, and a run-length version of the same idea reaches a halt as soon as block
sizes are forgotten, as it must, given `lean/Escape.lean`.

## Evidence and proofs

* `lean/Rules.lean` (kernel; generated by `py/rules.py` with `bbtools.symtm`): `feed0`, `feed1`, `feedb0`,
  `feedb1`, `hop0a`, `hop0b`, `hop1a`, `hop1b`, `birth0`, `birth1`, `birth2`, each for all sizes and every tape L to
  the left. `lean/Phase.lean`: the feeding rules restated and iterated (`feed2`, `feeds`).
* `lean/Escape.lean` (kernel): `esc_halts`, the tape above halts.
* `py/qsim.py` (trusted program, jumps heuristic): an exact rope simulator with macro rules for a^n, b and
  (b a^n)^q, plus jumps: when the same tape shape recurs with constant changes of the counts for 4 periods, many
  periods are applied at once and the next period is checked (rolled back and halved when it fails). Without jumps
  it agrees with a cell-by-cell simulator at each of the first 1,500 visits (`py/qsim_check.py direct 1500`; 6,000
  visits, 5.3x10^7 steps, were compared in the dedicated pass); with jumps it agrees with the run without jumps at
  every visit it stops at up to 3x10^10 steps (`py/qsim_check.py jumps 3e10`: 0 mismatches, 5 rollbacks).
  `python3 py/qsim.py 1e18`: **no halt in 10^18 steps** (3,304,842 visits simulated one by one, 127,033 jumps,
  160 s). The jumps are not proved, so this is an observation.
* `go/fsim.go` (trusted program, jumps heuristic): the same rope engine and macro rules, in Go with big integers,
  plus exact bulk feeding (the visits of one feeding run, until the block or the end block is used up, applied at
  once with their step count) and the periodic jumps over whole visits (validated by the period after each jump,
  rolled back and halved otherwise). Checks: `fsim 9 check0`, the plain engine against a cell-by-cell simulator of
  the table, tape and state at each of the 38,111 visits of the first 10^9 steps; `fsim 12 check1`, bulk feeding
  against the plain engine at each of 11,838 visits to 1.1x10^12 steps; `fsim 16 check2`, jumps against bulk feeding
  alone at 1,531 visits to 1.1x10^16 steps (20 jumps); and runs with other settings (`norun`, `nopack`, `four`)
  give the same tape (hash of the whole tape) at every visit they have in common between 10^300 and 10^400 steps
  (112,487, 112,310 and 112,524 visits; `fsim 400 quiet norun dump=F,300,400` and so on). `fsim 5000 quiet`: no halt
  in 10^5000 steps. The jumps keep every decreasing count above the threshold at which the shape would change, but
  the bulk feedings inside a period compare large counts with each other, which the shape does not record; that is
  why the jumps are checked afterwards and are not proofs.
* `py/births.py`, `py/escape.py`: the counts and the escaping tape above.

## What is open, and next steps

* A decision by computation alone looks out of reach: if the random model is right the machine never halts, and a
  halt, if there is one, comes far beyond 10^5000 steps.
* The global schedule: which cursor is where when a birth happens. A proof of non-halting needs to show that a
  birth never falls on the visit at which three 1s stand together (or that the next cursor then arrives as a 1); a
  proof of halting needs to find the time when it does. Either way the counter of equal blocks
  (127, 258, 1264, 70880, ...) has to be written as an exact recurrence, as in the sibling's outside proof.
* The rules for cursors side by side (`1 1`, `0 0`, `1 0`) are observed, not proved in Lean.

## Pages

- [`pages/holdouts/1RB1RF_1RC0RE_1LD0RB_1RE0LC_1RA0LE_0RC---/explainer.html`](../../pages/holdouts/1RB1RF_1RC0RE_1LD0RB_1RE0LC_1RA0LE_0RC---/explainer.html)
- [`pages/holdouts/1RB1RF_1RC0RE_1LD0RB_1RE0LC_1RA0LE_0RC---/proof-status.html`](../../pages/holdouts/1RB1RF_1RC0RE_1LD0RB_1RE0LC_1RA0LE_0RC---/proof-status.html)

## Check

```sh
M=holdouts/1RB1RF_1RC0RE_1LD0RB_1RE0LC_1RA0LE_0RC---
. /etc/profile.d/lean.sh && $M/lean/check.sh        # Rules, Phase, Escape (kernel)
python3 $M/py/rules.py > /tmp/Rules.lean            # regenerate lean/Rules.lean
python3 $M/py/qsim_check.py direct 1500             # macro rules against the plain machine
python3 $M/py/qsim_check.py jumps 3e8               # jumps on against jumps off (3e10: some minutes)
python3 $M/py/qsim.py 1e18                          # 10^18 steps, no halt (about 3 minutes)
python3 $M/py/births.py 1e18                        # births, and the one visit with three 1s (about 4 minutes)
python3 $M/py/escape.py                             # the tape of the block form that halts
(cd $M/go && go build -o /tmp/fsim .)               # Go 1.21 or later
/tmp/fsim 9 check0; /tmp/fsim 12 check1; /tmp/fsim 16 check2   # validations (seconds)
/tmp/fsim 5000 quiet                                # 10^5000 steps, no halt, the nine triples (about 30 minutes)
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0LE_1RC0LB_1RD1RF_1RE0RB_1LA0RD_0RE---`](../1RB0LE_1RC0LB_1RD1RF_1RE0RB_1LA0RD_0RE---/README.md): rename A→C, B→D, C→E, D→A, E→B, F→F; it is this table started in state D
- [`1RB0LE_1LC0RA_1LD0RC_1LE1LF_1LA0LC_0LA---`](../1RB0LE_1LC0RA_1LD0RC_1LE1LF_1LA0LC_0LA---/README.md): rename A→D, B→E, C→A, D→B, E→C, F→F and exchange left and right; it is this table started in state C, in a mirror

<!-- end of related machines -->
