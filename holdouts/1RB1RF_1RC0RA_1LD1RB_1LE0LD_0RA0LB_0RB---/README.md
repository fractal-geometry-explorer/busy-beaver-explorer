# 1RB1RF_1RC0RA_1LD1RB_1LE0LD_0RA0LB_0RB---

bbchallenge id 22262. G12 holdout, family: G12 word with two counters, 1RB?RF_1RC0RA_1LD1RB_1LE0LD_?L?0LB_0RB---. At every record a word of blocks with a last block growing by 2 and doubling time; halting only possible at rare rebuilds of the left end; open.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RF |
| B | 1RC | 0RA |
| C | 1LD | 1RB |
| D | 1LE | 0LD |
| E | 0RA | 0LB |
| F | 0RB | --- |

## Status

**The question is open.** Lean (kernel) proves the halting configurations, no halt in the first 10,000 steps (10^7 with `native_decide`) and three shift rules. Direct C runs find no halt in 2·10^10 steps and show the word-and-counter structure described below; the map of the left-end rebuilds, which is where a halt could happen, is not known.

### Lean, kernel

- **The halting configurations.** The machine stops exactly when it reads the symbol of a halting transition (F1); the generated statement covers every configuration. (`step_none_iff`, `lean/Blank.lean`)
- **No halt in the first 10,000 steps.** The list simulator of the shared library, proved to agree with the machine's semantics, runs 10,000 steps from blank tape without a halt, evaluated by Lean's kernel. (`blank_runs_kernel`, `lean/Blank.lean`)
- **Shift rules of the sweeps.** `W 0 1^3 0 1^(2k+1) B>0 0 → W 0 1 0 1 0 1 1 C> 0^(2k) 1` (head on the first of the 2k 0s) in `2k+11` steps (the last block erased after a record); `B> (10)^k → (01)^k B>` and `B> (01)^k → (11)^k B>` in `2k` steps. (`rec_erase`, `b_sweep10`, `b_sweep01`, `lean/Rules.lean`)

### Lean, native_decide

- **No halt in the first 10^7 steps.** The same run, evaluated by compiled code. (`blank_runs_native`, `lean/Blank.lean`)

### Trusted computation (C/Python, tested)

- **No halt in the first 10^9 steps.** The C simulator `tools/c/triage.c` runs 10^9 steps without a halt; at the end 249 cells have been visited and 135 of them hold a 1. (`holdouts/triage.json`)
- **No halt in the first 2·10^10 steps.** Direct C runs (`tools/c/tmrun.c`, and `c/fevents.c` of 1RB0RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_0LC---) reach 2·10^10 steps; there are 238 F events (A reading 1), each followed by a 0. (`tmrun MACHINE 20000000000 at B R`)

### Heuristic (observed, not proved)

- **Growth shape: exp/fixed.** Left of the start, the visited part of the tape stopped growing in the second half of the run (bounded so far, or growing so slowly that no record fell in the last half). Right of the start it grows like the logarithm of the step count: each new cell costs a roughly constant factor more time, the signature of a counter or of a Collatz-like map whose values are written on the tape (fitted exponent 0.016). (`tools/py/bbtools/triage.py`)
- **Records are words; time doubles.** At every record of the first 2·10^10 steps outside the left-end rebuilds the tape is a word ending in `1^n B>0`, `n` grows by 2 per record (to 57), the rest changes by one local rewrite, and the time between records tends to double. (records of the direct run)
- **Halting only at the left end.** A reads a 1 (the only way to F) only while the left end of the word is rebuilt, after the moving rewrite has reached it (some of these rebuilds are restarts of the last block). (F events of the direct run)

### Open

- **Does it halt from blank tape?.** Not known. The record-to-record map and the map of the left-end rebuilds have not been derived, so there is no accelerated simulation beyond direct runs.

## How it works

### At every record, a word

This machine and 1RB0RF_1RC0RA_1LD1RB_1LE0LD_1LB0LB_0RB--- differ only in A1 and E0, and they behave the same way. Each time the head reaches a new cell on the right (a record), the tape is a word: blocks of 1s separated by single 0s, ending in `1^n B>0`. For this machine, a short gadget with double 0s (`1 0 0 1 0 0 1 0 1 0 1 1 0 1 0 1 0 0` at the last record) sits at the left end, then the word. The blocks are odd, except that the first may be 2.

From one record to the next the last block grows by 2. The rest of the word changes by one small, width-preserving rewrite, at a place that moves one block to the left per record. The rewrites seen are `3 1 1 → 1 1 3`, `b → (b−2) 1`, `5 1 1 → 3 1 3`, `3 3 3 1 1 1 → 1 1 3 5 3` and a few others. The time between records tends to double. In the first 2·10^10 steps the last block reaches 57 (record at step 1.99·10^10).

### Two counters

Right after a record, state D erases the last block from right to left. Only a single marker 1 remains, `n+1` cells out. This is the Lean theorem `rec_erase`: `W 0 1^3 0 1^(2k+1) B>0 0` becomes `W 0 1 0 1 0 1 1 C> 0^(2k) 1` (the head on the first of the 2k 0s) in `2k+11` steps. The head then zigzags. Going left, it turns the single-1 blocks at the end of the word into units `1 1 0 0`. Going right, B sweeps them back, turning `10` into `01` and `01` into `11` (`b_sweep10`, `b_sweep01`). Meanwhile the empty stretch fills with gaps `1 0^odd`.

Between two records of 1RB0RF_1RC0RA_1LD1RB_1LE0LD_1LB0LB_0RB---, the turning points follow a ruler sequence on both sides of a fixed cell. On the right they go 88, 90, 88, 92, 88, 90, 88, 94, …. On the left they dig 55, 65, 41, 65, 55, 65, 45, … cells deep into the word. This is the signature of two binary counters running against each other: one written in the end of the word, one in the gaps. A full count takes about 2^n/2 steps, and it ends at the next record.

### Rebuilds and F events

F is reached only from A reading a 1, and F halts on a 1. So a halt needs A to read `1 1`. In the runs, A reads a 1 only when the moving rewrite reaches the left end of the word. There the machine rebuilds the left end. Some of these rebuilds also extend the word, and the last block starts again small (a restart). Records during a rebuild need not be words, and the F events come in bursts there. In the first 2·10^10 steps there are 238 F events, and each is followed by a 0.

Rebuilds are rare. For 1RB0RF_1RC0RA_1LD1RB_1LE0LD_1LB0LB_0RB--- the restarts come at about 5·10^3, 1.4·10^4, 3.1·10^5, 1.5·10^7, 9.7·10^7 and 7.0·10^9 steps. They are rare because the rewrite moves one block per record and records come ever more slowly, so direct simulation sees only a handful. Deciding the machine needs the exact record-to-record map on words, and from it the map of the left-end rebuilds. Neither is written down yet.

**Status: open.** Lean has the halting configurations, no halt in 10^7 steps, and three shift rules of the sweeps. The record structure is observed in direct runs, not proved.

## The proved neighbours (round 6)

The community tracker says: "One table, three starts, one entry away from a machine proved in merged PR 36. [...] The
rare entry keeps changing the head of the word, so the neighbour's invariant does not carry over."

- **The table and its starts.** This machine is one start of the table; `1RB0RE_1LC1RA_1LD0LC_0RE0LA_1RA1RF_0RA---` is the same table started in this machine's state B, and `1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE` is the mirrored table started in state D.
- **The neighbours.** `1RB1RF_1RC0RA_1LD1RB_1LE0LD_1LA0LB_0RB---`, `1RB1RF_1RC0RA_1LD1RB_1LE0LD_1LB0LB_0RB---` and `1RB1RF_1RC0RA_1LD1RB_1LE0LD_1RB0LB_0RB---` (E0 = `1LA`, `1LB`, `1RB`; here `0RA`), proved non-halting in busycoq pull request 36 (in the copy we read:
  `verify/PR_SOMDC_Class1.v`). They have this table except for the entry E0.
- **Is the entry used from blank tape?** Yes (trusted C++, `transcount`): first at step 6; 24 times in the first 10^10 steps (10 in the first 10^3, 18 in 10^4, 20 in 10^5, 22 in 10^6, 23 in 10^7, 24 in 10^9).
- **What it does here** (Lean, kernel, `lean/Halt.lean`). The entry fires when D, erasing 1s leftwards, reads a 0 with another 0 on its left: four steps later (D0, E0, A1, F0) the cells read `0 1 0` and B is on the next cell to the right.
  In the neighbours the same moment writes a 1 instead of the 0 and carries on differently.
- **Halting patterns** (Lean, kernel). `halt_c`: C reading a 0 with two 0s on its left (`0 0 C>0`) halts. `halt_b`: B reading `1 1 1` halts. Each is proved for every tape around the
  cells named. That these are the only two ways to halt is read backwards from the table, on paper.
- **Why the proof does not transfer.** It is not a matter of an unreached entry. The neighbours' proofs are long
  inductions over a word-and-counter description of each machine's own run (about 1,200 to 1,700 lines of Coq
  each); they depend on what the entry leaves at the left end of the word. Here the entry leaves `0 1 0` and sends
  the head right, where the neighbours extend the word. We did not find an invariant that survives this.

No proof was transferred. The decision stays open.

## Reproduce

From the repository root:

```sh
. /etc/profile.d/lean.sh      # after scripts/setup-lean.sh
holdouts/1RB1RF_1RC0RA_1LD1RB_1LE0LD_0RA0LB_0RB---/lean/check.sh
gcc -O2 -o tmrun tools/c/tmrun.c && ./tmrun 1RB1RF_1RC0RA_1LD1RB_1LE0LD_0RA0LB_0RB--- 20000000000 at B R 100000
python3 holdouts/1RB0RF_1RC0RA_1LD1RB_1LE0LD_1LB0LB_0RB---/py/gen_rules.py 1RB1RF_1RC0RA_1LD1RB_1LE0LD_0RA0LB_0RB---   # regenerates lean/Rules.lean
g++ -O2 -o transcount holdouts/1RB1RF_1RC0RA_1LD1RB_1LE0LD_0RA0LB_0RB---/c/transcount.cpp && ./transcount 1RB1RF_1RC0RA_1LD1RB_1LE0LD_0RA0LB_0RB--- 10000000000 E0
```

## For later

- Derive the exact record-to-record map on words (the two counters between records: the word's tail and the gaps `1 0^odd`), prove it with `bbtools.symtm` as was done for 1RB0RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_0LC---, and write an accelerated simulator; then study the left-end rebuilds, where every F event happens. Several days of work.
- Records and F events of the direct run: `tmrun MACHINE 20000000000 at B R 100000`; `c/fevents.c` in 1RB0RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_0LC--- prints every step at which A reads a 1.

## Pages

- `pages/holdouts/1RB1RF_1RC0RA_1LD1RB_1LE0LD_0RA0LB_0RB---/explainer.html`, `pages/holdouts/1RB1RF_1RC0RA_1LD1RB_1LE0LD_0RA0LB_0RB---/proof-status.html` (built by `python3 holdouts/build_pages.py 1RB1RF_1RC0RA_1LD1RB_1LE0LD_0RA0LB_0RB---`)

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0RE_1LC1RA_1LD0LC_0RE0LA_1RA1RF_0RA---`](../1RB0RE_1LC1RA_1LD0LC_0RE0LA_1RA1RF_0RA---/README.md): rename A→E, B→A, C→B, D→C, E→D, F→F; it is this table started in state B
- [`1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE`](../1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE/README.md): rename A→C, B→E, C→F, D→A, E→B, F→D and exchange left and right; it is this table started in state D, in a mirror

<!-- end of related machines -->
