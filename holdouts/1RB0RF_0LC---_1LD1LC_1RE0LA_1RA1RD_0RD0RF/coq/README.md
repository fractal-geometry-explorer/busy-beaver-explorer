# Coq: a halting proof that waits for a halt, and the engine run from start D

This machine is, mirrored and with its states renamed (A→D, B→F, C→A, D→B, E→C, F→E), the table

    U  = 1RB1RA_1LC0RD_1LD1LB_1LF0LE_0LB0LE_0RA---     started in state D

the table of the holdouts 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB0LF (start A), 1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA0RF
(start B) and 1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE0RF (start C). U is the table T3 of DeepMind's halting proof in
busycoq pull request 93 with T3's halt turned into a step and with a D0 detour that halts exactly when D reads 0 with
a 1 on its left. The reduction and the scripts are in
[`../../1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB0LF/coq/README.md`](../../1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB0LF/coq/README.md);
`mkU.py` there has a branch for this machine.

## What is proved (Coq 8.18.0, busycoq BB6 branch at 33209bc)

`mkU.py PR93.v U_D.v 1RB0RF_0LC---_1LD1LC_1RE0LA_1RA1RD_0RD0RF D 25 fast` writes a proof of `halts tm c0`; it
compiles, and `Print Assumptions halt` lists only

    HU.run_ok : HU.is_none (HU.run_pow 25 HU.initD) = true

the claim that the accelerated engine, started in D on blank tape, stops. A stop would complete the proof.

## The run (22 November 2026)

- **Validation (computed).** `validateU D 1100 3000000000`: 1,072 fast steps agree with direct simulation of U,
  through 3·10^9 machine steps.
- **No stop (computed).** The engine passed fast step 14,971,979 without stopping, on a tape of more than 2^4487
  cells, so **the machine does not halt in its first 10^1350 steps**. This rests on extracted code and OCaml, not on
  Coq's kernel. The method can only ever prove a halt.

`build.sh PR93.v OUTDIR` (with `BUSYCOQ` set) builds the skeleton and the tools; run them with `ulimit -s unlimited`
(`run D N CHECKPOINT`, `validateU D N M`).
