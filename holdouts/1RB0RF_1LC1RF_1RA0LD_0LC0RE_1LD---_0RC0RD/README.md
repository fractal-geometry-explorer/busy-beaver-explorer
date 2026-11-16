# 1RB0RF_1LC1RF_1RA0LD_0LC0RE_1LD---_0RC0RD

bbchallenge id 58767. Halting from blank tape is open. **The machine is a ternary counter on a list of gaps, and
halting is proved (Lean, kernel) to be equivalent to an explicit counter model reaching one of two patterns** (while
the counter stays inside its rules; with nothing assumed, to a hybrid model that falls back to machine steps outside them).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RF |
| B | 1LC | 1RF |
| C | 1RA | 0LD |
| D | 0LC | 0RE |
| E | 1LD | --- |
| F | 0RC | 0RD |

## What it does

Write the tape as **gap words** `0^g 1`. At the sample points (head in C next to `1 1 1` at the left end, about to
sweep right) the configuration is

    0^∞ 1 1 1 C> 0 0 1 [0^g1 1] [0^g2 1] ... [0^gk 1] 0^∞          state: the gap list [g1, ..., gk]

Most gaps are 3, so the list is blocks `3^m` (that is `(0001)^m`) separated by a few other gaps. Consecutive samples
from step 8,767 (`3^m` is a block, other numbers are single gaps):

    3^3  5     3^34 1 1 1  3^5  1 1 1 1 0
    3^4  1 1 1 3^35 1      3^5  1 1 1 1 0
    3^6  1     3^35 1      3^5  1 1 1 1 0
    3^7  5     3^34 1      3^5  1 1 1 1 0
    3^8  1 1 1 3^34 5      3^4  1 1 1 1 0

**One bounce rewrites the list** (proved, see below). C sweeps right, carrying `0 0 1`, over gaps 3 and 5, the pairs
(0, 1) and (2, 3) and the run (0, 0, 3, 3); at the first other pattern it turns back:

| stop | becomes | return |
|---|---|---|
| 1, x | x+2 | normal |
| 2, 1 | 3, 0 | normal |
| 0, x+2 | 1, 0, x | normal |
| 4, 1, x+2 | 1, 1, 1, 1, 0, x | normal |
| 2 / 0 at the end | 5, 1, 0 / 1, 0 | normal |
| x+7 | 1, 0, x+1 | special |
| 4 / 6 / 2, 0 at the end | 1, 1, 1, 1, 0 / 1, 0, 0 / 3, 0 | special |
| 0, 0, 0 or 4, 0 | the machine halts (E reads 1) | |

Going back, every 5 passed becomes 1 1 1. A passed (0, 1) is deleted and switches normal to special (special back
to normal, inserting 1 1 1); (0, 0, 3, 3) becomes 3, 0, 1 (normal, switching to special) or 5, 3 (special); (2, 3)
becomes 3, 0, 1 (normal) or 5, 3 (special, switching to normal). At the left end a normal return puts a 3 in front of
the list, a special one 1 1 1.

**It is a ternary counter.** Read the separators `1 1 1`, `1`, `5` between blocks as digits 2, 1, 0 (least
significant first). Then a bounce is a decrement: the zeros (5) below the first nonzero digit become 2 (1 1 1); a 2
becomes 1 and gives a 3 to the block before it; a 1 becomes 0 and takes a 3 from the block after it; the first block
gains one 3 per bounce. The separators `1 0 1`, `2 1`, `0` form a second kind of digit that never passes the borrow
on: each cycle of three moves a 3 from the block after it to the block before it, so it lasts until the block after
it runs out. Blocks that run out bring the rarer patterns (merges, the special return), and the end of the list
grows by the end-of-tape stops. This is the base-3 picture seen at the right extensions: blocks lose 6, 18, 54, 162
copies per cycle counted from the end.

## What is proved (Lean, kernel; `lean/check.sh` prints ALL CHECKED, no `sorry`)

- `lean/Counter.lean`: 29 symbolic pieces from `py/counter.py` (bbtools.symtm), and by hand the gap list
  semantics (`gw`, `gws`, `cfg`), the scan (`scanM`, `stopM`), the return (`retStep`, `retAll`), the left end
  (`finish`) and `bounceM`, with **`bounceM_next`** (a `next` of the model is a run of the machine of at least one
  step, for every gap list) and **`bounceM_halt`** (a `halt` is a halting configuration).
- `lean/Model.lean`: `blank_to_cfg` (blank tape reaches `cfg [1, 1, 1, 1, 0]` in 71 steps, kernel `decide`), and
  **`halts_iff_model`**: if the model started at `[1, 1, 1, 1, 0]` never gets `stuck`, the machine halts from blank
  tape **iff** the model reaches `halt`. Axioms: propext, Classical.choice, Quot.sound.
- `lean/Hybrid.lean` (12 November): the model made total. `hstep` makes a bounce of the gap counter where `bounceM`
  is defined and a single machine step (on the configuration written out as two lists) where it is `stuck`.
  **`halts_iff_hybrid`: the machine halts from blank tape iff the hybrid run from `[1, 1, 1, 1, 0]` reaches `halt`,
  with no hypothesis.** `hrun_of_runM`: while the gap counter is not stuck the hybrid run is the gap counter's run.
  `model_runs_kernel` / `model_runs_native`: 200 / 30,000 bounces of the gap counter without halt or stuck. The
  fallback explains nothing about the uncovered patterns; it only removes the hypothesis from the statement.
- `lean/Rules.lean` (`py/rules.py`): the plain sweep rules; `lean/Blank.lean`: halting configurations, no halt in
  10^4 (kernel) / 10^7 (native) steps.

## Checked, not proved

- `c/gapdump.c` reads the gap list off the real machine at every sample point; `py/model.py check` confirms the
  model (run-length version) at all 129,587 bounces up to 2·10^10 steps, and the flat transcription of the Lean
  definitions (`bounce_lean`) on the first 2,979.
- `py/model.py far` (many bounces per step: ternary-counter jumps, checked against single bounces for 3·10^7
  bounces, and periodic extrapolation, each one re-run over one period at the far end): no halt and no stuck pattern in 870 s, about 10^89 bounces; the list grows to 371 entries, the first blocks to about 90 digits.

## Why the rules were not completed (12 November)

Every uncovered stop pattern tried (leading gaps up to 9, three deep, 840 cases) makes the machine come back in the
normal or special return mode, or halt; none leaves the picture. But they are not a short table: some are further
passable tokens (2, 2 is passed and becomes 3, 0, 3), and a cell-level search for a complete decision tree does not
close at depth 16. Completing the gap-level model needs a second layer of sweep rules; an invariant that keeps the
run inside the covered patterns is not known.

## Open

Halting: whether the counter ever reaches the gaps (0, 0, 0) or (4, 0), or a pattern outside the model. Like the
other base-3 counters this looks Collatz-like; nothing suggests a halt.

## Reproduce

```sh
tools/c/tokrun 1RB0RF_1LC1RF_1RA0LD_0LC0RE_1LD---_0RC0RD 20000000000 c=1110,s=111111 R 2000     # the list at right extensions
python3 holdouts/1RB0RF_1LC1RF_1RA0LD_0LC0RE_1LD---_0RC0RD/py/rules.py > holdouts/1RB0RF_1LC1RF_1RA0LD_0LC0RE_1LD---_0RC0RD/lean/Rules.lean
python3 holdouts/1RB0RF_1LC1RF_1RA0LD_0LC0RE_1LD---_0RC0RD/py/counter.py      # the pieces in lean/Counter.lean
gcc -O2 -o gapdump holdouts/1RB0RF_1LC1RF_1RA0LD_0LC0RE_1LD---_0RC0RD/c/gapdump.c && ./gapdump 20000000000 > m2g.txt
python3 holdouts/1RB0RF_1LC1RF_1RA0LD_0LC0RE_1LD---_0RC0RD/py/model.py check m2g.txt
python3 holdouts/1RB0RF_1LC1RF_1RA0LD_0LC0RE_1LD---_0RC0RD/py/model.py far 870
. /etc/profile.d/lean.sh && holdouts/1RB0RF_1LC1RF_1RA0LD_0LC0RE_1LD---_0RC0RD/lean/check.sh
```

## Long accelerated run (16 November 2026)

**No halt in the first 2.16·10^37 steps** (trusted, bounded): step 21,622,797,242,713,355,695,099,328,749,058,417,170,
which is 4.02·10^18 bounces, with 38 digits at the end. No step of this run is extrapolated, unlike the heuristic
10^89-bounce run of `py/model.py far`. It is a second, independent model: it does not use the gap counter's
rules or the hybrid model.

- `py/digits.py`: an exact model at the sample points of `cfg` (one per bounce). It reads the tape **mirrored**
  and reuses the generic window engine of `holdouts/1RB0LF_1LC0RC_1RA1LD_0RB0LE_1LC0LB_---1LA/py/digits.py`
  (class `Spec`) on the mirror machine `1LB0LF_1RC1LF_1LA0RD_0RC0LE_1RD---_0LC0LD`, with the sample changed to
  the head on 0 with `1 1 1` and blank tape to its right. Runs are runs of gaps 3. The walls are T2 = gaps 1 1 1,
  T1 = gap 1 and T0 = gap 5 (ternary digits 2, 1, 0; the borrow passes T0), and any other block becomes a wall of
  its own name. Each bounce is a **symbolic run of the machine** (`tools/py/bbtools/symtm.py`) on a window around
  the borrow chain, with long runs as variables. So the uncovered stop patterns of "Why the rules were not
  completed" are not needed: every window shape that comes up is run by the machine itself.
- `py/accel.py`: that holdout's `py/macro4.py` (hierarchical macros, cycle skips only within classes).
- Checks: `python3 py/digits.py check DUMP` against `c/gapdump` (`./gapdump 1000000000`): all 29,691 bounces up to
  10^9 steps agree exactly, gap lists and step counts. `python3 py/accel.py test DUMP 1000000`: macros and 17
  cycle skips agree with single bounces over 1.07·10^6 bounces.
- The run (`python3 py/accel.py run DUMP 1800 CKPT.pkl`, from the last sample of `./gapdump 3000000`) never
  stopped: no symbolic rule halted (E reading 1), needed a case split or failed to parse. It is slower than the
  other machines' runs: 1.7·10^6 macros were derived, and only 8,470 macro applications were made, because most
  macro keys did not recur. End state: `/mnt/project-files/halt-hunt/f06left/1RB0RF_1LC1RF_1RA0LD_0LC0RE_1LD---_0RC0RD_state_2.16e37.pkl`.

## Pages

- [`pages/holdouts/1RB0RF_1LC1RF_1RA0LD_0LC0RE_1LD---_0RC0RD/explainer.html`](../../pages/holdouts/1RB0RF_1LC1RF_1RA0LD_0LC0RE_1LD---_0RC0RD/explainer.html)
- [`pages/holdouts/1RB0RF_1LC1RF_1RA0LD_0LC0RE_1LD---_0RC0RD/proof-status.html`](../../pages/holdouts/1RB0RF_1LC1RF_1RA0LD_0LC0RE_1LD---_0RC0RD/proof-status.html)

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0LD_1RC0RF_1LA1RF_0LA0RE_1LD---_0RA0RD`](../1RB0LD_1RC0RF_1LA1RF_0LA0RE_1LD---_0RA0RD/README.md): rename A→B, B→C, C→A, D→D, E→E, F→F; it is this table started in state C
- [`1RB1LD_1LC0RE_1LA0LD_0LB0LE_0RB0LF_1RE---`](../1RB1LD_1LC0RE_1LA0LD_0LB0LE_0RB0LF_1RE---/README.md): rename A→C, B→A, C→B, D→E, E→F, F→D and exchange left and right; it is this table started in state B, in a mirror
- [`1RB---_0RC0LA_1LD0RB_1LE0LF_1RC1LF_0LC0LB`](../1RB---_0RC0LA_1LD0RB_1LE0LF_1RC1LF_0LC0LB/README.md): rename A→D, B→E, C→C, D→B, E→A, F→F and exchange left and right; it is this table started in state E, in a mirror

<!-- end of related machines -->
