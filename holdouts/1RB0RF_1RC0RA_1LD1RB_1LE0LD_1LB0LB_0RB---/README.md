# 1RB0RF_1RC0RA_1LD1RB_1LE0LD_1LB0LB_0RB---

bbchallenge id 29824. G12 holdout, family: G12 word with two counters, 1RB?RF_1RC0RA_1LD1RB_1LE0LD_?L?0LB_0RB---. At every record a word of blocks with a last block growing by 2 and doubling time; halting only possible at rare rebuilds of the left end; open.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RF |
| B | 1RC | 0RA |
| C | 1LD | 1RB |
| D | 1LE | 0LD |
| E | 1LB | 0LB |
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

- **No halt in the first 10^9 steps.** The C simulator `tools/c/triage.c` runs 10^9 steps without a halt; at the end 214 cells have been visited and 112 of them hold a 1. (`holdouts/triage.json`)
- **No halt in the first 2·10^10 steps.** Direct C runs (`tools/c/tmrun.c`, and `c/fevents.c` of 1RB0RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_0LC---) reach 2·10^10 steps; there are 133 F events (A reading 1), each followed by a 0. (`tmrun MACHINE 20000000000 at B R`)

### Heuristic (observed, not proved)

- **Growth shape: exp/fixed.** Left of the start, the visited part of the tape stopped growing in the second half of the run (bounded so far, or growing so slowly that no record fell in the last half). Right of the start it grows like the logarithm of the step count: each new cell costs a roughly constant factor more time, the signature of a counter or of a Collatz-like map whose values are written on the tape (fitted exponent 0.071). (`tools/py/bbtools/triage.py`)
- **Records are words; time doubles.** At every record of the first 2·10^10 steps outside the left-end rebuilds the tape is a word ending in `1^n B>0`, `n` grows by 2 per record (to 51), the rest changes by one local rewrite, and the time between records tends to double. (records of the direct run)
- **Halting only at the left end.** A reads a 1 (the only way to F) only while the left end of the word is rebuilt, after the moving rewrite has reached it (some of these rebuilds are restarts of the last block). (F events of the direct run)

### Open

- **Does it halt from blank tape?.** Not known. The record-to-record map and the map of the left-end rebuilds have not been derived, so there is no accelerated simulation beyond direct runs.

## How it works

### At every record, a word

This machine and 1RB1RF_1RC0RA_1LD1RB_1LE0LD_0RA0LB_0RB--- differ only in A1 and E0, and they behave the same way. Each time the head reaches a new cell on the right (a record), the tape is a word: blocks of 1s separated by single 0s, ending in `1^n B>0`. For this machine, the word starts at the left end of the visited tape. The blocks are odd, except that the first may be 2.

From one record to the next the last block grows by 2. The rest of the word changes by one small, width-preserving rewrite, at a place that moves one block to the left per record. The rewrites seen are `3 1 1 → 1 1 3`, `b → (b−2) 1`, `5 1 1 → 3 1 3`, `3 3 3 1 1 1 → 1 1 3 5 3` and a few others. The time between records tends to double. In the first 2·10^10 steps the last block reaches 51 (record at step 1.57·10^10).

### Two counters

Right after a record, state D erases the last block from right to left. Only a single marker 1 remains, `n+1` cells out. This is the Lean theorem `rec_erase`: `W 0 1^3 0 1^(2k+1) B>0 0` becomes `W 0 1 0 1 0 1 1 C> 0^(2k) 1` (the head on the first of the 2k 0s) in `2k+11` steps. The head then zigzags. Going left, it turns the single-1 blocks at the end of the word into units `1 1 0 0`. Going right, B sweeps them back, turning `10` into `01` and `01` into `11` (`b_sweep10`, `b_sweep01`). Meanwhile the empty stretch fills with gaps `1 0^odd`.

Between two records of 1RB0RF_1RC0RA_1LD1RB_1LE0LD_1LB0LB_0RB---, the turning points follow a ruler sequence on both sides of a fixed cell. On the right they go 88, 90, 88, 92, 88, 90, 88, 94, …. On the left they dig 55, 65, 41, 65, 55, 65, 45, … cells deep into the word. This is the signature of two binary counters running against each other: one written in the end of the word, one in the gaps. A full count takes about 2^n/2 steps, and it ends at the next record.

### Rebuilds and F events

F is reached only from A reading a 1, and F halts on a 1. So a halt needs A to read `1 1`. In the runs, A reads a 1 only when the moving rewrite reaches the left end of the word. There the machine rebuilds the left end. Some of these rebuilds also extend the word, and the last block starts again small (a restart). Records during a rebuild need not be words, and the F events come in bursts there. In the first 2·10^10 steps there are 133 F events, and each is followed by a 0.

Rebuilds are rare. For 1RB0RF_1RC0RA_1LD1RB_1LE0LD_1LB0LB_0RB--- the restarts come at about 5·10^3, 1.4·10^4, 3.1·10^5, 1.5·10^7, 9.7·10^7 and 7.0·10^9 steps. They are rare because the rewrite moves one block per record and records come ever more slowly, so direct simulation sees only a handful. Deciding the machine needs the exact record-to-record map on words, and from it the map of the left-end rebuilds. Neither is written down yet.

**Status: open.** Lean has the halting configurations, no halt in 10^7 steps, and three shift rules of the sweeps. The record structure is observed in direct runs, not proved.

## Reproduce

From the repository root:

```sh
. /etc/profile.d/lean.sh      # after scripts/setup-lean.sh
holdouts/1RB0RF_1RC0RA_1LD1RB_1LE0LD_1LB0LB_0RB---/lean/check.sh
gcc -O2 -o tmrun tools/c/tmrun.c && ./tmrun 1RB0RF_1RC0RA_1LD1RB_1LE0LD_1LB0LB_0RB--- 20000000000 at B R 100000
python3 holdouts/1RB0RF_1RC0RA_1LD1RB_1LE0LD_1LB0LB_0RB---/py/gen_rules.py 1RB0RF_1RC0RA_1LD1RB_1LE0LD_1LB0LB_0RB---   # regenerates lean/Rules.lean
```

## For later

- Derive the exact record-to-record map on words (the two counters between records: the word's tail and the gaps `1 0^odd`), prove it with `bbtools.symtm` as was done for 1RB0RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_0LC---, and write an accelerated simulator; then study the left-end rebuilds, where every F event happens. Several days of work.
- Records and F events of the direct run: `tmrun MACHINE 20000000000 at B R 100000`; `c/fevents.c` in 1RB0RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_0LC--- prints every step at which A reads a 1.

## Pages

- `pages/holdouts/1RB0RF_1RC0RA_1LD1RB_1LE0LD_1LB0LB_0RB---/explainer.html`, `pages/holdouts/1RB0RF_1RC0RA_1LD1RB_1LE0LD_1LB0LB_0RB---/proof-status.html` (built by `python3 holdouts/build_pages.py 1RB0RF_1RC0RA_1LD1RB_1LE0LD_1LB0LB_0RB---`)

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0RE_1LC1RA_1LD0LC_1LA0LA_1RA0RF_0RA---`](../1RB0RE_1LC1RA_1LD0LC_1LA0LA_1RA0RF_0RA---/README.md): rename A→E, B→A, C→B, D→C, E→D, F→F; it is this table started in state B
- [`1RB0RA_1RC0RC_1LD0LE_1RA1LC_1LC0LF_0LC---`](../1RB0RA_1RC0RC_1LD0LE_1RA1LC_1LC0LF_0LC---/README.md): rename A→E, B→C, C→D, D→A, E→B, F→F and exchange left and right; it is this table started in state D, in a mirror
- [`1RB0RB_1LC0LE_1RD1LB_1RA0RD_1LB0LF_0LB---`](../1RB0RB_1LC0LE_1RD1LB_1RA0RD_1LB0LF_0LB---/README.md): rename A→E, B→B, C→C, D→D, E→A, F→F and exchange left and right; it is this table started in state E, in a mirror

<!-- end of related machines -->
