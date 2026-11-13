# 1RB1LB_1RC1LE_1RD0LF_0LA0RD_---1LD_0LD1LF

bbchallenge id 111363. One of the six-state holdouts whose halting from blank tape is open. Its pages are [`pages/holdouts/1RB1LB_1RC1LE_1RD0LF_0LA0RD_---1LD_0LD1LF/explainer.html`](../../pages/holdouts/1RB1LB_1RC1LE_1RD0LF_0LA0RD_---1LD_0LD1LF/explainer.html) and [`pages/holdouts/1RB1LB_1RC1LE_1RD0LF_0LA0RD_---1LD_0LD1LF/proof-status.html`](../../pages/holdouts/1RB1LB_1RC1LE_1RD0LF_0LA0RD_---1LD_0LD1LF/proof-status.html), built from [`status.json`](status.json).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LB |
| B | 1RC | 1LE |
| C | 1RD | 0LF |
| D | 0LA | 0RD |
| E | --- | 1LD |
| F | 0LD | 1LF |

Family: **One machine and its shadow, 3-cell binary counters (G12 family 3a)**.

## What it does

The shadow of `1RB1LE_1RC1LD_1RD0LF_0LA0RD_---1LB_0LD1LF` (T): Lean proves the two make the same run, step for step, until A reads a 1 with a 0 one or two cells further left; there exactly one of them halts (`lean/Family.lean`). The C simulator runs the shared part S for 10^11 steps without that happening. The mechanism (a hierarchy of binary counters with 3-cell digits) is described in T's folder.

## What is established

**Proved in Lean, kernel only:**

- **The halting configurations.** The machine stops exactly when it reads the symbol of a halting transition (E0); the generated statement covers every configuration. (`step_none_iff`, `lean/Blank.lean`)
- **No halt in the first 10,000 steps.** The list simulator of the shared library, proved to agree with the machine's semantics, runs 10,000 steps from blank tape without a halt, evaluated by Lean's kernel. (`blank_runs_kernel`, `lean/Blank.lean`)
- **M3 is T with its states renamed.** `1RB1LC_1RC0LF_0LD0RC_1RA1LE_---1LA_0LC1LF` is `1RB1LE_1RC1LD_1RD0LF_0LA0RD_---1LB_0LD1LF` with the states renamed A→D, B→A, C→B, D→C (every transition, halts included), so its run from blank tape is the run of `1RB1LE_1RC1LD_1RD0LF_0LA0RD_---1LB_0LD1LF` started in state B on blank tape: one 1 fewer at the left than T's own run after its first step. `m3_iff`. (`lean/Family.lean`)
- **T and M1 make the same run until a 0 sits within two cells left of A reading a 1.** The two machines differ only in the 1-transitions of A, B and E, which all write 1 and move left. The seven-state machine S = `1RB1LE_1RC---_1RD0LF_0LA0RD_---1LG_0LD1LF_---1LD` is the part they share (B split into B entered from A0 and E entered from A1). Every step S makes, both make on the same tape (`shadow`); in S, B entered from A0 always reads a 0, because A is entered only by D0 = 0LA (`star_good`); so S stops only where A has read a 1 and then meets a 0 one cell (S's E0) or two cells (S's G0) further left, and there exactly one of T and M1 halts and the other goes on with B0 = 1RC (`deviation`). Hence S halts iff T or M1 halts (`star_halts_iff`), and if neither halts they make the same run step for step (`same_run`). (`lean/Family.lean`, `lean/Link.lean`)

**Proved in Lean with `native_decide`:**

- **No halt in the first 10^7 steps.** The same run, evaluated by compiled code. (`blank_runs_native`, `lean/Blank.lean`)
- **T and M1 agree for the first 10^7 steps.** S runs 10^7 steps from blank tape without stopping (and 10,000 checked by the kernel), so by `shadow` the two machines have the same tape and head at each of those steps. (`star_runs_native`, `same_first_steps`, `1RB1LE_1RC1LD_1RD0LF_0LA0RD_---1LB_0LD1LF`/`lean/Link.lean`)

**Trusted computation (C/Python, not Lean):**

- **No halt in the first 10^9 steps.** The C simulator `tools/c/triage.c` runs 10^9 steps without a halt; at the end 163 cells have been visited and 95 of them hold a 1. (`holdouts/triage.json`)
- **No halt in the first 10^11 steps.** `tools/c/tmrun.c` runs 100,000,000,000 steps without a halt; the head reached 199 cells on the left side and 175 on the right (record positions). (`tools/c/tmrun.c MACHINE 100000000000 records 1000000`)
- **T and M1 agree for the first 10^11 steps.** The C simulator runs S for 10^11 steps without a stop; with the Lean simulation theorem this means the two machines make the same run through 10^11 steps (which is why their record outputs were identical). (`tmrun 1RB1LE_1RC---_1RD0LF_0LA0RD_---1LG_0LD1LF_---1LD 100000000000` (7.5 minutes))

**Heuristic:**

- **The tape (as T's).** Same run as T for 10^11 steps, so the same structure: At a typical moment the left part is a list of binary numbers written with digits 000 and 111, each section starting with a 111 and separated from the next by a single 0; the sections are incremented like the digits of one mixed-radix counter (the rightmost section, next to where the head works, changes every ~850 steps, the leftmost once per count of the epoch). To their right sit long runs of 1s separated by single 0s (e.g. 1^13, 1^18, 1^22), which change only at the stretch boundaries (1^22 became 1^16, then 1^10), and a short tail that changes once per epoch, like a third counter level. So the run is a hierarchy of counters, each level ticking when the one below overflows. The rules of the middle levels have not been found. (`tmrun ... every`, snapshots)

**Open:**

- **Does it halt from blank tape?** Not known. It halts only where the shared part S stops on G0 (proved); whether T's run ever produces that pattern depends on the higher counter levels of T, whose rules are not known.

## For later

Everything about this machine now reduces to T: see T's README.

## Reproduce

```sh
. /etc/profile.d/lean.sh      # after scripts/setup-lean.sh
holdouts/1RB1LB_1RC1LE_1RD0LF_0LA0RD_---1LD_0LD1LF/lean/check.sh
gcc -O2 -o tmrun tools/c/tmrun.c && ./tmrun 1RB1LB_1RC1LE_1RD0LF_0LA0RD_---1LD_0LD1LF 100000000000 records 1000000
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same run as [`1RB1LE_1RC1LD_1RD0LF_0LA0RD_---1LB_0LD1LF`](../1RB1LE_1RC1LD_1RD0LF_0LA0RD_---1LB_0LD1LF/README.md) (observed, not proved).** At every one of the first 10^7 steps from blank tape the two machines have the same tape and the head on the same cell. Their tables differ, and no renaming of the states turns one into the other. While they run, the states pair up as A–A, B–B, B–E, C–C, D–D, E–B, F–F (this machine first), which is not one to one. Transitions not used in these steps: this machine never uses E0 and the other never uses E0. Lean proves (`lean/Twin.lean` here, `lock_or_break`, `not_halts_of_noBreak`) that the two runs have the same tape, the same head position and paired states up to the first break, a configuration where the paired states act differently, and that neither machine halts if no break ever comes. A halt of either machine is itself a break, and the halting transitions of the two do not correspond, so the two are not known to halt together.

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0LE_0LC0RB_1RD1LD_1RA1LF_0LB1LE_---1LB`](../1RB0LE_0LC0RB_1RD1LD_1RA1LF_0LB1LE_---1LB/README.md): rename A→C, B→D, C→A, D→B, E→F, F→E; it is this table started in state C

<!-- end of related machines -->
