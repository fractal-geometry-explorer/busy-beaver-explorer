# Coq (busycoq) proof that the machine halts

```coq
Theorem halt : halts tm c0.        (* H155900.v; tm := TM_from_str "1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA0RF_0LD---" *)
```

On busycoq's own definitions (`TM`, `halts`, `c0`). `Print Assumptions halt` prints `Closed under the global
context`. Coq 8.18.0 compiles the file in about 33 minutes (`build.log`), nearly all of it one evaluation checked by
the kernel's VM (`run_ok`).

## Where it comes from

The proof is DeepMind's proof of busycoq pull request 93 (module `M598`, Alex Havrilla, 17 November 2026), changed
for this machine. That pull request proves that the table `1RB1RA_1LC0RD_1LD1LB_1RA0LE_0LB0LF_0LB---` halts from
state C, with a *fast engine*: a function on run-length tapes of macro words whose every step is proved sound, run
until it reaches a halting configuration. This machine is, mirrored and with states renamed (A→D, B→A, C→B, D→C),
the table `1RB1RA_1LC0RD_1LD1LB_1RA0LE_0LB0LF_0RA---` (T4) started in state B. T4 differs from PR 93's table only in
F0 (`0RA` instead of `0LB`).

Four of the engine's base rules pass through F0. For T4 they end in configuration `<B 1` with `11` more on the right
instead of `<C 100` (`rule_collision`, `rule_collide`, `rule_finishP`, `rule_defect0`; the same four are proved in
Lean in `holdouts/1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0LC---/lean/T4Rules.lean`). The file restates these four and
redoes every lemma and engine case built on them: the collision and defect calls, the returns over `PL` words and
`DefWord a 0`, the immediate defects of mode `MR`, the collisions of mode `ML` and the fast right sweep, whose T4 form
needs one more guard (`la ≥ 1`). All of it is proved; nothing is admitted.

The engine, started on the blank tape in source state B, reaches a halting configuration (head in F on a 1) after
261,156 of its steps, on a tape of about 2^2410 cells; `run_ok` checks `run_pow 19` (2^19 steps, it stops at the
halt). The machine's own step count is not computed here.

## Files

- `H155900.v`: the proof (generated, 5,728 lines).
- `build.sh /path/to/busycoq`: copies it into a checkout of busycoq's BB6 branch, compiles it and prints the
  assumptions.
- `build.log`: the compile here.
- The generator is in `tools/coq/t4engine/proof` (`mk.py` applies the engine patch `../patch.py` to PR 93's file
  and retargets the table, `lem.py` redoes the lemmas); `sh tools/coq/t4engine/proof/build.sh /path/to/busycoq`
  regenerates `H155900.v` byte for byte from a checkout holding PR 93's `verify/M_1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0RDHHH.v`.
  With `fast` as second argument it admits `run_ok` and compiles in about 30 seconds.
