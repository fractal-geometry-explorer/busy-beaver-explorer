# 1RB1RC_1RC1RB_1LD0RA_1LE1LD_1LF0LC_0LA---

bbchallenge id 144803. One of the six-state holdouts whose halting from blank tape is open. **It rewrites a long list
of blocks of 1s, almost all of length `4k + 3` with `k` spread like a fair coin's run lengths; each round multiplies
the length of the list by about 1.75.** No closed-form rule is found yet; this folder records what was seen.

**Update, 22 November 2026: the rule is known.** This is the Pascal machine
`1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF` in a mirror, started in its state C. A block `1^(4k+3) 0` is the word
`v^k u` in that machine's letters, each bounce is one row of Pascal's triangle mod 2, and halting reduces in Lean to
that machine's list program from another start. See "Pascal's triangle, in a mirror" below; the older text up to
there is kept as it was.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RC |
| B | 1RC | 1RB |
| C | 1LD | 0RA |
| D | 1LE | 1LD |
| E | 1LF | 0LC |
| F | 0LA | --- |

## What it does (observed)

The visited part of the tape lies right of the start; its left end moves by a cell or two per round. At the moments
the head reaches a new cell at the left end (`D> 0 1^a 0 1^b 0 …`), the tape is a list of blocks of 1s separated by
single 0s. Apart from the first two blocks and the last one, **every block has length `4k + 3`** (checked at each of
these moments up to step 5.2·10⁸), and the values of `k` are spread like the run lengths of fair coin flips: at step
522,867,988 there are 5,366 blocks, 2,665 with `k = 0`, 1,336 with `k = 1`, 716, 315, 160, 88, 47, 22, … for
`k = 2, 3, …` (each count about half the one before).

Between those moments the head sweeps across the whole list. A sweep to the right rewrites each block `1^(4k+3)`
into a string of short runs (`1 0 1 0 …` with longer runs between), and the sweep back to the left rewrites it into
blocks again, so the list changes as a whole (`c/turns.c` prints the tape at every reversal of the head). Bursts of
short sweeps near the left end alternate with long full sweeps. The *rounds*, the long gaps between visits of the
left end, start at

    step           blocks   Σ(k+1)
    3,664          14       26
    45,100         54       97
    584,746        183      351
    5,887,250      574      1,136
    55,865,122     1,794    3,508
    522,867,988    5,366    10,746

so each round multiplies `Σ(k+1)` (the length of the list read as a word in which block `4k + 3` stands for `k`
ones and a zero) by about 1.75 and the step count by about 3.1. A round costs about the square of the tape length,
so the tape grows like the square root of the step count on the right and slowly on the left: the exp/sqrt shape
the triage saw.

## Does it halt?

(As first written; superseded by the mirror section below.) Open. Proved (Lean): only the generated facts in `lean/Blank.lean` (the halting configurations; no halt in 10⁷
steps). Computed: no halt in 10⁹ steps (`tools/c/triage.c`, and `c/sim.c`). The rule of a round is not known, so
neither is where a halt (state F reading a 1) could come from; no heuristic is given. The coin-like spread of the
block lengths suggests that the list behaves like a pseudo-random word that the rounds rewrite, as in the
Collatz-like holdouts.

## For later

More than a day of work remains. (1) Read the list as the binary word above (block `4k + 3` ↦ `1^k 0`) and look for
the map a round applies to it: the ratio 1.75 is close to √3, so test whether two rounds multiply a number written
in that word by 3 (or by 3/2 and by 2), in some base and bit order. (2) Find the sweep rules (each block's image in
a right sweep, the carries in a left sweep) and prove them with `symtm`. (3) Find the configurations that reach F on
a 1, and what they mean for the word.

## Files

- `c/sim.c`: plain simulation from blank tape, printing the edge events.
- `c/turns.c`: the tape at every reversal of the head, between two step counts.

## Pascal's triangle, in a mirror (22 November 2026)

This table is the table of [`1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF`](../1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF/README.md)
(the "Pascal machine") read in a mirror, with that machine's states A, B, C, D, E, F renamed E, F, A, B, C, D
(`is_mirror`, `lean/Mirror.lean`). The blank tape is its own mirror image, so **this machine's run from blank tape
is, cell for cell in the mirror, the run of the Pascal table started in state C** (`halts_iff`). Everything proved
about the Pascal table holds for any surrounding tape, so it holds here with left and right exchanged. Read in this
machine's own terms:

* The Pascal machine's left sweep (running parity, in its states C and D) is the sweep right in A/B here, its right
  sweep (in E and F) the sweep left in C/D, and its right turn (E reading a 1) is a **left turn in C** here. The zone that is rewritten every bounce lies right of the head, next to the growing
  right end. The frozen tape lies left of the head, toward the start.
* `bounce` (Lean): at a left turn in C, with the zone a word in the 4-cell letters `0111` (1) and `1111` (0) read
  outward from the head, and the frozen tape `1 1 1 ...` left of the head, one bounce turns the zone into the next row
  of Pascal's triangle mod 2 and takes two cells from the frozen block. `bounces`: a frozen block of `2k + 1` cells
  gives `k` bounces. The rows have a closed form by Lucas' theorem (`closed_form` of `lean/P75625/Lucas.lean`, a
  statement about lists that holds as it stands).
* `halts_of_odd`, `halts_of_odd_wall` (Lean): a left turn in C at a frozen block of odd length followed by `0 1`
  halts, whatever the zone, clean or walled. That is the halt of `halt_route` (D reading 0 with `0` and then `1` to
  its left), reached by bouncing an odd block down to a single 1.
* `start` (Lean): the first left turn in C is at step 26, the list state `EO [b, a, b, a] none 1` of the
  Pascal machine's list machine (`lean/P75625/End.lean`): C on the last 1 at the left end, zone `b a b a`, prefix
  1. The Pascal machine's own run starts the same list machine at `EO [b, a] none 1`.
* `not_halts_of_arun` (Lean): **if that list machine never fails from `EO [b, a, b, a] none 1`, this machine
  never halts.** So this holdout is the same list program as the Pascal machine, started in another state. Every
  further theorem about the list machine (the Pascal machine's folder works on it) settles both.

How it was done: rather than restating every proof with the sides exchanged, `py/port_mirror.py` copies the Pascal
machine's Lean files unchanged into `lean/P75625/` (only their imports are renamed, so they compile next to this
folder's `Machine.lean`), and `lean/Mirror.lean` carries the theorems over with the mirror lemmas of
`tools/lean/TM/Insert.lean`. Rerun the script after that folder's files change. Kernel only, no `native_decide`.

**Where the list machine can fail (`lean/Fail.lean`, kernel, for every state).** A turn with no lone 1 in the zone
(`T`, or `EO` outside a crossing) never fails (`astep_T`, `astep_EO`). A crossing turn whose far part is clean and
whose tape ends in a single 1 never fails (`astep_T2_end`). Plain and crossing turns whose tape ends in a single 1
pass that on (`astep_endOne`), so a blank end comes only after an `EO` turn (the head on the last 1). Together
(`astep_none`): the list machine fails only at a crossing turn with blank end, at an `EO` turn during a crossing, or
at a crossing turn whose far part is not clean. This is about the Pascal machine's list machine, so it holds for all
three runs.

**The list machine from this start (`py/mirror_run.py`, computed).** Run on its own from `start`, the list machine takes 40,000 list steps without failing (17,772 `T` turns, 22,209 `T2` turns, 19 `EO` turns, zone up to 21,498 letters, every far part clean), about 14 minutes. None of the 19 `EO` turns comes during a crossing, so no state with blank end ever arises (a crossing turn with blank end needs an earlier `EO` turn during a crossing: `astep_endOne` for plain and crossing turns ending in one 1, and a plain turn with blank end only becomes a crossing turn at the end of the tape, where `endS` marks the end again; read off `astep`, not a separate Lean statement) and the first failure case cannot occur at all in that stretch: unlike the other two runs, there is not one crossing turn with blank end. What is left is to show that no `EO` turn ever comes during a crossing (then only an unclean far part could make it fail). Run in lockstep with the real machine (`python3 py/mirror_run.py lockstep C 2e8`), the list machine agrees at all 17,728 right turns of the first 2·10^8 steps of the Pascal table started in C.

**10^6 list steps (`c/mirror_lm.sh C 1000000` in the folder of
1RB1RA_1LC0RF_1LD1LC_1LE0LB_0LF---_1RA1RB, a few minutes).** The Pascal machine's C++ list machine, started here,
takes 10^6 list steps without failing (zone up to 623,187 letters). Still no `EO` turn comes during a crossing (27
`EO` turns, all outside crossings), so not one crossing turn with blank end occurs. The Pascal machine's window
theorems (`lean/P75625/Window.lean`) are compiled here too but are not needed for this run so far.

## Status

Open. It halts if and only if the Pascal table started in C halts (Lean). If the Pascal machine's list machine never
fails from `EO [b, a, b, a] none 1`, it never halts (Lean). See the section above.

Open. The claims with what each rests on are in `status.json` and the proof-status page.

## Deciders tried (F11, 13 November 2026)

None closes. Each reaches a halting configuration in its abstraction, which says nothing about halting.

- n-gram CPS (`tools/c/ngramcps.c`), equal widths on both sides: a halting local configuration is reached with plain up to width 24, history 1 up to width 24, history 2 up to width 24, history 3 up to width 24, LRU history up to width 6 (larger widths ran out of the 150 s or 60 million configuration budget).
- n-gram CPS with every cell tagged by its position mod p: fails for p = 2 up to width 20, p = 3 up to width 20, p = 4 up to width 20, p = 6 up to width 20.
- n-gram CPS where each side also carries the state of a small automaton that has read that side from the far end (every automaton with up to 3 states on both sides, or 4 states on one side), with position mod 1..4 and widths 4, 6, 8: no closed set without a halt in all 120 parameter sets.
- Run-length windows (the K nearest runs of equal macro cells on each side, run lengths kept exactly below T and mod M above): fails for all 72 parameter sets (cells of 1 to 4 bits, K = 2, 4, 6, T = 2, 4, M = 1, 2, 4).
- Two-automaton closed tape language by SAT (a deterministic automaton reading each side inward, n states each, CaDiCaL): no solution for n = 2..7; n = 8 not finished in 150 s.

## Where a halt can come from

`lean/Route.lean` (kernel, written by `py/route.py`): `halt_route`, two steps before any halt the machine is in one
of: D with 1 two left, 0 left, 0 under the head.

## Pages

- [`pages/holdouts/1RB1RC_1RC1RB_1LD0RA_1LE1LD_1LF0LC_0LA---/explainer.html`](../../pages/holdouts/1RB1RC_1RC1RB_1LD0RA_1LE1LD_1LF0LC_0LA---/explainer.html)
- [`pages/holdouts/1RB1RC_1RC1RB_1LD0RA_1LE1LD_1LF0LC_0LA---/proof-status.html`](../../pages/holdouts/1RB1RC_1RC1RB_1LD0RA_1LE1LD_1LF0LC_0LA---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RC_1RC1RB_1LD0RA_1LE1LD_1LF0LC_0LA---/lean/check.sh
python3 holdouts/1RB1RA_1LC0RF_1LD1LC_1LE0LB_0LF---_1RA1RB/py/port_mirror.py      # refresh lean/P75625, Mirror.lean (both folders)
python3 holdouts/1RB1RA_1LC0RF_1LD1LC_1LE0LB_0LF---_1RA1RB/py/mirror_run.py run C 40000   # the list machine, ~15 min
python3 holdouts/1RB1RA_1LC0RF_1LD1LC_1LE0LB_0LF---_1RA1RB/py/mirror_run.py lockstep C 2e8
holdouts/1RB1RA_1LC0RF_1LD1LC_1LE0LB_0LF---_1RA1RB/c/mirror_lm.sh C 1000000      # C++ list machine
gcc -O2 -o sim holdouts/1RB1RC_1RC1RB_1LD0RA_1LE1LD_1LF0LC_0LA---/c/sim.c && ./sim 1RB1RC_1RC1RB_1LD0RA_1LE1LD_1LF0LC_0LA--- 1000000000 1 | grep ' LD '
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB1RA_1LC0RF_1LD1LC_1LE0LB_0LF---_1RA1RB`](../1RB1RA_1LC0RF_1LD1LC_1LE0LB_0LF---_1RA1RB/README.md): rename A→F, B→A, C→B, D→C, E→D, F→E; it is this table started in state B
- [`1RB0LE_1RC1RB_1RD0RA_0RE---_1LF1LA_1LA1LF`](../1RB0LE_1RC1RB_1RD0RA_0RE---_1LF1LA_1LA1LF/README.md): rename A→E, B→F, C→A, D→B, E→C, F→D and exchange left and right; it is this table started in state C, in a mirror
- [`1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF`](../1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF/README.md): rename A→C, B→D, C→E, D→F, E→A, F→B and exchange left and right; it is this table started in state E, in a mirror

**Same tapes at another pace (observed, not proved).** Leave the states aside and compare only the tape and the place of the head. Then a large part of the first 10^7 configurations of this machine are configurations of the machines below, in the same order and up to the end of the run. The steps at which they occur differ, the tables are not renamings of each other, and equal tapes with different states may be continued differently, so this does not tie the halting questions together.

- [`1RB0RB_1LC---_0LA1LD_1RE0LC_1RF1RE_1RA0RD`](../1RB0RB_1LC---_0LA1LD_1RE0LC_1RF1RE_1RA0RD/README.md) (in a mirror): 4,990,813 configurations, the last at step 6,660,591 here and step 10,000,000 there

<!-- end of related machines -->
