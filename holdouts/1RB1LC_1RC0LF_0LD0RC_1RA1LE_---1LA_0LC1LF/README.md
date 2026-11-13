# 1RB1LC_1RC0LF_0LD0RC_1RA1LE_---1LA_0LC1LF

bbchallenge id 72232. One of the six-state holdouts whose halting from blank tape is open. Its pages are [`pages/holdouts/1RB1LC_1RC0LF_0LD0RC_1RA1LE_---1LA_0LC1LF/explainer.html`](../../pages/holdouts/1RB1LC_1RC0LF_0LD0RC_1RA1LE_---1LA_0LC1LF/explainer.html) and [`pages/holdouts/1RB1LC_1RC0LF_0LD0RC_1RA1LE_---1LA_0LC1LF/proof-status.html`](../../pages/holdouts/1RB1LC_1RC0LF_0LD0RC_1RA1LE_---1LA_0LC1LF/proof-status.html), built from [`status.json`](status.json).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LC |
| B | 1RC | 0LF |
| C | 0LD | 0RC |
| D | 1RA | 1LE |
| E | --- | 1LA |
| F | 0LC | 1LF |

Family: **One machine and its shadow, 3-cell binary counters (G12 family 3a)**.

## What it does

`1RB1LE_1RC1LD_1RD0LF_0LA0RD_---1LB_0LD1LF` (T) with its states renamed (A→D, B→A, C→B, D→C), so its run from blank tape is T's run from blank tape in state B (`lean/Family.lean`, `lean/Link.lean`). The mechanism (a hierarchy of binary counters with 3-cell digits) is described in T's folder; this run has the same structure with other contents.

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

- **No halt in the first 10^9 steps.** The C simulator `tools/c/triage.c` runs 10^9 steps without a halt; at the end 152 cells have been visited and 99 of them hold a 1. (`holdouts/triage.json`)
- **No halt in the first 10^11 steps.** `tools/c/tmrun.c` runs 100,000,000,000 steps without a halt; the head reached 189 cells on the left side and 174 on the right (record positions). (`tools/c/tmrun.c MACHINE 100000000000 records 1000000`)
- **T and M1 agree for the first 10^11 steps.** The C simulator runs S for 10^11 steps without a stop; with the Lean simulation theorem this means the two machines make the same run through 10^11 steps (which is why their record outputs were identical). (`tmrun 1RB1LE_1RC---_1RD0LF_0LA0RD_---1LG_0LD1LF_---1LD 100000000000` (7.5 minutes))

**Open:**

- **Does it halt from blank tape?** Not known. It halts iff T started in state B halts (proved); the rules of T's higher counter levels are not known, so there is no argument either way.

## For later

Reduces to T started in state B: the same decoding work as for T, then rerun from this start.

## Reproduce

```sh
. /etc/profile.d/lean.sh      # after scripts/setup-lean.sh
holdouts/1RB1LC_1RC0LF_0LD0RC_1RA1LE_---1LA_0LC1LF/lean/check.sh
gcc -O2 -o tmrun tools/c/tmrun.c && ./tmrun 1RB1LC_1RC0LF_0LD0RC_1RA1LE_---1LA_0LC1LF 100000000000 records 1000000
```
