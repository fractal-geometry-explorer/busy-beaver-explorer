# The T4 engine: DeepMind's PR 93 engine retargeted to three open holdouts

Three holdouts of the 608 are one machine table started in three different states:

| holdout | bbchallenge id | source state |
|---|---|---|
| `1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA0RF_0LD---` | 155900 | D |
| `1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0LC---` | 127983 | C |
| `1RB0LE_1RC1RB_1LD0RA_1LA1LC_0LC0LF_0RB---` | 67137 | B |

The source table is `1RB1RA_1LC0RD_1LD1LB_1RA0LE_0LB0LF_0RA---` (call it T4). Each holdout is this table, mirrored
and with its states renamed, and started in the state given. It differs in one transition (F0: `0RA` here, `0LB`
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

Only the definitions are patched. The soundness proofs of PR 93 are not redone for T4, so the patched engine is
**not a proof**. It is checked against direct simulation instead (`validate`).

## Files

- `strip.py` keeps only the definitions of PR 93's file (`Definition`, `Fixpoint`, `Inductive`, `Record`).
- `patch.py` replaces the two tables and makes the changes above; each change is one exact string replacement.
- `extra.v` adds the finite denotation `fs_list` (for validation) and the starts in states B and D.
- `ExtT4C.v` extracts the engine to OCaml; `run.ml` and `validate.ml` are the drivers.
- `build.sh /path/to/busycoq` does all of this (Coq 8.18, OCaml with `ocamlfind`).

Run both with `ulimit -s unlimited`: the extracted list functions are not tail-recursive.

`run START N` runs `N` fast steps from blank tape in source state `START` (B, C or D). When no engine rule
applies, it says whether the configuration is a halt (F1) or a gap of the engine. `validate START N M` runs the
source table directly next to the engine. After each fast step, it requires the direct run to reach exactly the
engine's configuration (state, head cell and every tape cell) within `M` steps in all.

## Results (18 November 2026)

- The unpatched engine, extracted the same way, reproduces PR 93's halt of the T3 machine (2,452,242 fast steps, 4.5 minutes).
- For T4, `validate` agrees with direct simulation from all three starts: start C through 9.7·10¹⁰ direct steps
  (1,451 fast steps) with the version before the fast right sweep, and through 1.27·10¹⁰ steps with it; starts B
  and D through 3·10⁹ steps.
- No start has stopped yet: see the status pages of the three holdouts for the current count.
