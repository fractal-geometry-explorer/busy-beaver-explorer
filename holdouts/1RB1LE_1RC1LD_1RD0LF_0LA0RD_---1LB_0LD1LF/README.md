# 1RB1LE_1RC1LD_1RD0LF_0LA0RD_---1LB_0LD1LF

bbchallenge id 51101. One of the six-state holdouts whose halting from blank tape is open. Its pages are [`pages/holdouts/1RB1LE_1RC1LD_1RD0LF_0LA0RD_---1LB_0LD1LF/explainer.html`](../../pages/holdouts/1RB1LE_1RC1LD_1RD0LF_0LA0RD_---1LB_0LD1LF/explainer.html) and [`pages/holdouts/1RB1LE_1RC1LD_1RD0LF_0LA0RD_---1LB_0LD1LF/proof-status.html`](../../pages/holdouts/1RB1LE_1RC1LD_1RD0LF_0LA0RD_---1LB_0LD1LF/proof-status.html), built from [`status.json`](status.json).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LE |
| B | 1RC | 1LD |
| C | 1RD | 0LF |
| D | 0LA | 0RD |
| E | --- | 1LB |
| F | 0LD | 1LF |

Family: **One machine and its shadow, 3-cell binary counters (G12 family 3a)**.

## What it does

Lean proves that this machine is the core of a family of three holdouts: `1RB1LC_1RC0LF_0LD0RC_1RA1LE_---1LA_0LC1LF` is this machine with renamed states started in state B, and `1RB1LB_1RC1LE_1RD0LF_0LA0RD_---1LD_0LD1LF` makes the same run until one of them halts (`lean/Family.lean`, the same file in all three folders). It halts iff its run reaches F reading 0 or B reading 1 with `0 1 0` on the left (`lean/Halt.lean`).

The run is a hierarchy of counters. Digits are 3-cell blocks (`000`, `111`); the left part is a binary counter written this way in sections separated by single 0s; a small engine region in the middle adds 1 to it at an exactly regular rate; when the counter is all ones the head crosses it to the left edge, wipes it and restarts it with one more digit, so epochs double exactly. Long runs of 1s in the middle (unary numbers) and a tail at the right change at epoch and stretch boundaries; their rules are not known.

## What is established

**Proved in Lean, kernel only:**

- **The halting configurations.** The machine stops exactly when it reads the symbol of a halting transition (E0); the generated statement covers every configuration. (`step_none_iff`, `lean/Blank.lean`)
- **No halt in the first 10,000 steps.** The list simulator of the shared library, proved to agree with the machine's semantics, runs 10,000 steps from blank tape without a halt, evaluated by Lean's kernel. (`blank_runs_kernel`, `lean/Blank.lean`)
- **What a halt has to look like.** The machine halts from blank tape iff its run reaches F reading a 0, or B reading a 1, with the cells 0, 1, 0 to the left of the head (nearest first); the halt (E0) follows four steps later. Reason: E is entered only from A1, A only from D0, and D moving right always has the wrong cell on its left (C, entered only by B0 = 1RC, always has a 1 on its left), so the chain D0, A1, E0 must start with D moving left onto 0, 1, 0. Proved by an invariant and a check of every state and seven-cell neighbourhood. (`halts_iff`, `1RB1LE_1RC1LD_1RD0LF_0LA0RD_---1LB_0LD1LF`/`lean/Halt.lean`)
- **M3 is T with its states renamed.** `1RB1LC_1RC0LF_0LD0RC_1RA1LE_---1LA_0LC1LF` is `1RB1LE_1RC1LD_1RD0LF_0LA0RD_---1LB_0LD1LF` with the states renamed A→D, B→A, C→B, D→C (every transition, halts included), so its run from blank tape is the run of `1RB1LE_1RC1LD_1RD0LF_0LA0RD_---1LB_0LD1LF` started in state B on blank tape: one 1 fewer at the left than T's own run after its first step. `m3_iff`. (`lean/Family.lean`)
- **T and M1 make the same run until a 0 sits within two cells left of A reading a 1.** The two machines differ only in the 1-transitions of A, B and E, which all write 1 and move left. The seven-state machine S = `1RB1LE_1RC---_1RD0LF_0LA0RD_---1LG_0LD1LF_---1LD` is the part they share (B split into B entered from A0 and E entered from A1). Every step S makes, both make on the same tape (`shadow`); in S, B entered from A0 always reads a 0, because A is entered only by D0 = 0LA (`star_good`); so S stops only where A has read a 1 and then meets a 0 one cell (S's E0) or two cells (S's G0) further left, and there exactly one of T and M1 halts and the other goes on with B0 = 1RC (`deviation`). Hence S halts iff T or M1 halts (`star_halts_iff`), and if neither halts they make the same run step for step (`same_run`). (`lean/Family.lean`, `lean/Link.lean`)

**Proved in Lean with `native_decide`:**

- **No halt in the first 10^7 steps.** The same run, evaluated by compiled code. (`blank_runs_native`, `lean/Blank.lean`)
- **T and M1 agree for the first 10^7 steps.** S runs 10^7 steps from blank tape without stopping (and 10,000 checked by the kernel), so by `shadow` the two machines have the same tape and head at each of those steps. (`star_runs_native`, `same_first_steps`, `1RB1LE_1RC1LD_1RD0LF_0LA0RD_---1LB_0LD1LF`/`lean/Link.lean`)

**Trusted computation (C/Python, not Lean):**

- **No halt in the first 10^9 steps.** The C simulator `tools/c/triage.c` runs 10^9 steps without a halt; at the end 163 cells have been visited and 95 of them hold a 1. (`holdouts/triage.json`)
- **No halt in the first 10^11 steps.** `tools/c/tmrun.c` runs 100,000,000,000 steps without a halt; the head reached 199 cells on the left side and 175 on the right (record positions). (`tools/c/tmrun.c MACHINE 100000000000 records 1000000`)
- **T and M1 agree for the first 10^11 steps.** The C simulator runs S for 10^11 steps without a stop; with the Lean simulation theorem this means the two machines make the same run through 10^11 steps (which is why their record outputs were identical). (`tmrun 1RB1LE_1RC---_1RD0LF_0LA0RD_---1LG_0LD1LF_---1LD 100000000000` (7.5 minutes))
- **The halting pattern never comes close in 2·10^9 steps.** Among the 1.3·10^8 times F reads a 0 in the first 2·10^9 steps, the left cells are 000, 001 or 111 except 15 times (110 three times, 011 twelve times, the last at step 3,650,798); B reads a 1 with 0,1 on its left 49 times, always followed by 1. The halting pattern 0,1,0 never occurs. (`1RB1LE_1RC1LD_1RD0LF_0LA0RD_---1LB_0LD1LF`/`c/near.c`)
- **Epochs: a binary counter at the left end whose period doubles.** The head reaches the left end only in state F, crossing a run 1^n (n = 3k+1 after the start) that is the left counter at all ones; D then erases it, leaving 1^3 0^(3k) 1^2, i.e. the counter reset with one more 3-cell digit. Between two such moments the counter counts through 2^k values. In each stretch of the run the steps per count are a constant: 851.5, 27345.5, 7377.5, 2385.5 and (from step 1.86·10^10) 154.375, exactly, epoch after epoch (e.g. epochs of 312,672,261, 625,344,501, 1,250,689,029, 2,501,378,037 and 5,002,756,119 steps); at the stretch boundaries the middle of the tape is rearranged. 29 epochs are listed, the last ending at step 98,851,039,064 with n = 88. (`tmrun T 100000000000 at F L`, `1RB1LE_1RC1LD_1RD0LF_0LA0RD_---1LB_0LD1LF`/`py/epochs.py`, `py/epochs_1e11.txt`)

**Heuristic:**

- **The tape: binary counters in 3-cell digits, unary registers in the middle.** At a typical moment the left part is a list of binary numbers written with digits 000 and 111, each section starting with a 111 and separated from the next by a single 0; the sections are incremented like the digits of one mixed-radix counter (the rightmost section, next to where the head works, changes every ~850 steps, the leftmost once per count of the epoch). To their right sit long runs of 1s separated by single 0s (e.g. 1^13, 1^18, 1^22), which change only at the stretch boundaries (1^22 became 1^16, then 1^10), and a short tail that changes once per epoch, like a third counter level. So the run is a hierarchy of counters, each level ticking when the one below overflows. The rules of the middle levels have not been found. (`tmrun ... every`, snapshots)

**Open:**

- **Does it halt from blank tape?** Not known. Halting needs the pattern 0, 1, 0 left of a leftward D (proved), which would have to be produced by one of the higher counter levels; their rules are not known, so there is no argument either way, not even a heuristic one.

## For later

Decode the higher levels: at each epoch boundary the tail right of the middle changes, and at each stretch boundary (steps per count 851.5 → 27345.5 → 7377.5 → 2385.5 → 154.375) the middle runs of 1s are rewritten. Cut the run at the left-end visits (`py/epochs.py`), write the middle and the tail as numbers, find the map between consecutive stretches, then prove the per-count cycle of the engine and the counter increment with `bbtools.symtm` (one rule per stretch, with the counter's trailing ones `(111)^t` as a variable) to get an accelerated simulator past 10^11 steps. `lean/Halt.lean` says what to look for: the pattern 0 1 0 left of a leftward D.

## Reproduce

```sh
. /etc/profile.d/lean.sh      # after scripts/setup-lean.sh
holdouts/1RB1LE_1RC1LD_1RD0LF_0LA0RD_---1LB_0LD1LF/lean/check.sh
gcc -O2 -o tmrun tools/c/tmrun.c && ./tmrun 1RB1LE_1RC1LD_1RD0LF_0LA0RD_---1LB_0LD1LF 100000000000 records 1000000
python3 holdouts/1RB1LE_1RC1LD_1RD0LF_0LA0RD_---1LB_0LD1LF/py/family.py check
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same run as [`1RB1LB_1RC1LE_1RD0LF_0LA0RD_---1LD_0LD1LF`](../1RB1LB_1RC1LE_1RD0LF_0LA0RD_---1LD_0LD1LF/README.md) (observed, not proved).** At every one of the first 10^7 steps from blank tape the two machines have the same tape and the head on the same cell. Their tables differ, and no renaming of the states turns one into the other. While they run, the states pair up as A–A, B–B, B–E, C–C, D–D, E–B, F–F (this machine first), which is not one to one. Transitions not used in these steps: this machine never uses E0 and the other never uses E0. Lean proves (`lean/Twin.lean` in the other machine's folder, `lock_or_break`, `not_halts_of_noBreak`) that the two runs have the same tape, the same head position and paired states up to the first break, a configuration where the paired states act differently, and that neither machine halts if no break ever comes. A halt of either machine is itself a break, and the halting transitions of the two do not correspond, so the two are not known to halt together.

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB1LC_1RC0LF_0LD0RC_1RA1LE_---1LA_0LC1LF`](../1RB1LC_1RC0LF_0LD0RC_1RA1LE_---1LA_0LC1LF/README.md): rename A→D, B→A, C→B, D→C, E→E, F→F; it is this table started in state B

<!-- end of related machines -->
