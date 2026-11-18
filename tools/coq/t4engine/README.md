# The T4 engine: DeepMind's PR 93 engine retargeted to three open holdouts

Three holdouts of the 608 are one machine table started in three different states:

| holdout | bbchallenge id | source state |
|---|---|---|
| `1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA0RF_0LD---` | 155900 | B (halts, proved in Coq: see below) |
| `1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0LC---` | 127983 | C |
| `1RB0LE_1RC1RB_1LD0RA_1LA1LC_0LC0LF_0RB---` | 67137 | D |

The source table is `1RB1RA_1LC0RD_1LD1LB_1RA0LE_0LB0LF_0RA---` (call it T4). Each holdout is this table with its
states renamed (and mirrored, for the first two), started in the state given. It differs in one transition (F0: `0RA` here, `0LB`
there) from the table of `1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0RD---`, which DeepMind proved halts in
[busycoq PR 93](https://github.com/ccz181078/busycoq/pull/93) (module `M598`). That proof runs a fast engine, an
evaluator over run-length tapes of macro words, whose every step is proved sound in Coq.

## What changes for T4

The engine works with three configurations: `CfgR l r = l A> 0100 r`, `CfgL l r = l <B 1 r` and
`CfgJ l r = l <C 100 r`. All of PR 93's macro rules hold for T4 except the ones that end in `CfgJ`, because these
pass through F0. For T4 they end in `CfgL` instead, with `11` more on the right: `CfgJ l X` becomes
`CfgL l (11 X)`. With `11 · D n = D (n+1)` for the digit word `D n = 1 (11)^n 00`, this moves the `+1` carry from
the digit on the left to the digit on the right. The four basic rules are proved in Lean for the holdout
1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0LC---
(`holdouts/1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0LC---/lean/T4Rules.lean`):

| PR 93 rule (T3) | T4 form |
|---|---|
| `rule_collision`: `CfgL (001101 l) r → CfgJ l (1111 r)` | `CfgL l (111111 r)` (`t4_collision`) |
| `rule_collide`: `CfgR l (10 D0 D0 r) → CfgJ l (D2 10 r)` | `CfgL l (D3 10 r)` (`t4_collide`) |
| `rule_finishP`: `… → CfgJ l (D (1+b) r)` | `CfgL l (D (2+b) r)` (`t4_finishP`) |
| `rule_defect0`: `… → CfgJ l (1111 (D m) 1 r)` | `CfgL l (111111 (D m) 1 r)` (`t4_defect0`) |

`patch.py` changes the engine at every place that uses one of these rules or a rule built on them:

- the collision calls (`call (D j 10 D0 D0 r) (D j D3 10 r)`; T3 gives `D (1+j) D2`) and the defect call;
- the immediate defects of `stepMR_imm` and the collisions of `stepML_col`, which now go to mode `ML`;
- the returns over a `PL` word (`returnP_L`, `returnP_J`) and the `DefWord a 0` returns (`def_k0_ML`), in
  `sweepLeftOne`, `sweepLeftBlank`, `handleDefInSweep` and `sweepLeftBlankDef1`;
- the fast right sweep `trySweepMR_a0`. Its T4 forms were found by simulation (all checked cases agree): over
  `DefWord la lk` the sweep leaves `S (m+3) · DefWord la (lk-3)` (T3: `S (m+2) · DefWord (la+1) (lk-3)`); after an
  `S sn` it leaves `S (m+3) · S sn · …` (T3: `S (m+2) · S (sn+1) · …`); over a `PL n` it leaves
  `S (m+3) · DefWord (n+4) (2n-2)` (T3: `DefWord (n+5) …`).

The sweep over `DefWord la lk` needs `la ≥ 1` for T4 (it goes through `def_restart`); `patch.py` adds that guard.

`patch.py` patches only the definitions, and the extracted engine is checked against direct simulation
(`validate`). For the start that halts, the soundness proofs are redone as well: `proof/` turns PR 93's file into a
complete Coq proof for 1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA0RF_0LD--- (see Results).

## Files

- `strip.py` keeps only the definitions of PR 93's file (`Definition`, `Fixpoint`, `Inductive`, `Record`).
- `patch.py` replaces the two tables and makes the changes above; each change is one exact string replacement.
- `extra.v` adds the finite denotation `fs_list` (for validation), the size `fs_cells` and the starts in states B and D.
- `ExtT4C.v` extracts the engine to OCaml; `run.ml` and `validate.ml` are the drivers, `peek.ml` prints the mode,
  the head and the first runs of a checkpoint.
- `proof/`: `mk.py` and `lem.py` write the Coq proof of the halt; `proof/build.sh /path/to/busycoq [fast]`.
- `build.sh /path/to/busycoq` does all of this (Coq 8.18, OCaml with `ocamlfind`).

Run both with `ulimit -s unlimited`: the extracted list functions are not tail-recursive.

`run START N [CHECKPOINT]` runs `N` fast steps from blank tape in source state `START` (B, C or D), printing the
size of the tape as a power of 2 every minute. With a checkpoint file it saves its state there every 10 minutes and
resumes from it. When no engine rule applies it stops; `peek CHECKPOINT` then shows whether the head is in F on a 1
(a halt) or the engine has a gap. `validate START N M` runs the
source table directly next to the engine. After each fast step, it requires the direct run to reach exactly the
engine's configuration (state, head cell and every tape cell) within `M` steps in all.

## Results (18 November 2026)

- The unpatched engine, extracted the same way, reproduces PR 93's halt of the T3 machine (2,452,242 fast steps, 4.5 minutes).
- For T4, `validate` agrees with direct simulation from all three starts: start C through 9.7·10¹⁰ direct steps
  (1,451 fast steps) with the version before the fast right sweep, and through 1.27·10¹⁰ steps with it; starts B
  and D through 3·10¹⁰ steps.
- Start B (1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA0RF_0LD---) stops after 261,156 fast steps, on a tape of about 2^2410
  cells, with the head in state F on a 1: a halt. The engine with the `la ≥ 1` guard stops at the same step.
- `proof/` makes this a Coq theorem, `halt : halts tm c0` for that machine on busycoq's definitions, with no
  axioms (`Print Assumptions`: closed under the global context; Coq 8.18.0, 33 minutes). The file and its build
  script are in `holdouts/1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA0RF_0LD---/coq`.
- Starts C and D have not stopped: see the status pages of those two holdouts for the current count.
