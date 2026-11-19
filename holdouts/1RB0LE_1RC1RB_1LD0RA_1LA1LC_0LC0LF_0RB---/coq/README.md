# Coq (busycoq) proof that the machine halts

```coq
Theorem halt : halts tm c0.        (* H67137.v; tm := TM_from_str "1RB0LE_1RC1RB_1LD0RA_1LA1LC_0LC0LF_0RB---" *)
```

On busycoq's own definitions (`TM`, `halts`, `c0`). `Print Assumptions halt` (the last line of the file) prints
`Closed under the global context`. Coq 8.18.0 compiled it here in 44,430 s, about 12 hours (`build.log`); nearly all
of it is one evaluation checked by the kernel's VM (`run_ok`).

## Why it halts

With states renamed (A→B, B→C, C→D, D→A, no mirror), this machine is the table
`1RB1RA_1LC0RD_1LD1LB_1RA0LE_0LB0LF_0RA---` (T4) started in state D. T4 differs only in F0 from the table that
DeepMind proved halting in busycoq pull request 93. The proof is the one of 1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA0RF_0LD---
(T4 started in B, `holdouts/1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA0RF_0LD---/coq`): that pull request's fast engine with
the four rules that pass through F0 changed and every lemma built on them redone. Here the table, the state map, the
start and the isomorphism (no `flip`) change, and the final run is `run_pow 20` (2^20 steps at most) instead of 19.
From state D the proved engine reaches a halting configuration of T4 (F on a 1) after 688,228 engine steps, on a tape
of about 2^6326 cells. The machine's own step count is not computed here.

## Files

- `H67137.v`: the proof (generated, 5,728 lines): `H155900.v` with those changes.
- `build.sh /path/to/busycoq`: copies it into a checkout of busycoq's BB6 branch and compiles it.
- `build.log`: the compile here.
- The generator is `tools/coq/t4engine/proof/mkD.py`, applied to the output of `mk.py` and `lem.py`
  (`sh tools/coq/t4engine/proof/build.sh /path/to/busycoq` writes all four files).
