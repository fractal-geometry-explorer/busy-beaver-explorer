# Coq (busycoq) proof that the machine halts

```coq
Theorem halt : halts tm c0.        (* H181655.v; tm := TM_from_str "1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB0LE" *)
```

On busycoq's own definitions (`TM`, `halts`, `c0`). `Print Assumptions halt` (the last line of the file) prints
`Closed under the global context`. Coq 8.18.0 compiled it here in 6,573 s with two other long jobs on the machine
(`build.log`); nearly all of it is one evaluation checked by the kernel's VM (`run_ok`).

## Why it halts

Exchange the names of E and F. The table becomes `1RB1RA_1LC0RD_1LD1LB_1LF0LE_0LB0LF_0RA---`, which is the table
`1RB1RA_1LC0RD_1LD1LB_1RA0LE_0LB0LF_0RA---` (T4) in every transition except D0. T4's D0 is `1RA`. Here D0 is a
detour: `1LE`, and then, if the cell left of the head is 0, E0 `0RA` and A1 `1RA`. Those three steps end in exactly
the configuration T4's single step reaches. If that cell is 1, E reads it and the machine halts. So the run of this
machine is T4's run from blank tape in state A, slowed down, except that it may halt earlier; every halt of T4 is a
halt here. The lemma `detour` proves this for every configuration and every number of steps.

T4 started in A halts. T4 is the table of the holdouts 1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA0RF_0LD--- (start B, proved
halting in `holdouts/1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA0RF_0LD---/coq`),
1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0LC--- (start C) and 1RB0LE_1RC1RB_1LD0RA_1LA1LC_0LC0LF_0RB--- (start D), one
transition away from the table DeepMind proved halting in busycoq pull request 93. The proof for start B is that
pull request's fast engine changed for T4; here the same proof runs from start A. The engine reaches a halting
configuration of T4 (F on a 1) after 350,227 engine steps, on a tape of about 2^3562 cells. Whether this machine
halts there or earlier, at a detour that meets a 1, the proof does not say.

## Files

- `H181655.v`: the proof (generated, 5,750 lines): `H155900.v` with the table, the start (A) and the final step
  changed, and `perm_src`/`halts_iso` replaced by `detour`.
- `build.sh /path/to/busycoq`: copies it into a checkout of busycoq's BB6 branch and compiles it.
- `build.log`: the compile here.
- The generator is `tools/coq/t4engine/proof/mkA.py`, applied to the output of `mk.py` and `lem.py`
  (`sh tools/coq/t4engine/proof/build.sh /path/to/busycoq` writes both files).
