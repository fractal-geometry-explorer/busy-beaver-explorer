# Coq (busycoq) proof that the machine halts

```coq
Theorem halt : halts tm c0.        (* H127983.v; tm := TM_from_str "1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0LC---" *)
```

On busycoq's own definitions (`TM`, `halts`, `c0`). `Print Assumptions halt` (the last line of the file) prints
`Closed under the global context`. Coq 8.18.0 compiled it here in 14,145 s, with a long engine run on the same
machine (`build.log`); nearly all of it is one evaluation checked by the kernel's VM (`run_ok`).

## Why it halts

This machine is, mirrored and with states renamed (A→C, B→D, C→A, D→B), the table
`1RB1RA_1LC0RD_1LD1LB_1RA0LE_0LB0LF_0RA---` (T4) started in state C. T4 differs only in F0 from the table that
DeepMind proved halting in busycoq pull request 93. The proof is the one of 1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA0RF_0LD---
(T4 started in B, `holdouts/1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA0RF_0LD---/coq`): that pull request's fast engine with
the four rules that pass through F0 changed and every lemma built on them redone. Only the table, the state map and
the start change. From state C the proved engine reaches a halting configuration of T4 (F on a 1) after 427,055
engine steps, on a tape of about 2^4360 cells. The machine's own step count is not computed here.

## Files

- `H127983.v`: the proof (generated, 5,730 lines): `H155900.v` with the table, `permState` and the start changed.
- `build.sh /path/to/busycoq`: copies it into a checkout of busycoq's BB6 branch and compiles it.
- `build.log`: the compile here.
- The generator is `tools/coq/t4engine/proof/mkC.py`, applied to the output of `mk.py` and `lem.py`
  (`sh tools/coq/t4engine/proof/build.sh /path/to/busycoq` writes all three files).
