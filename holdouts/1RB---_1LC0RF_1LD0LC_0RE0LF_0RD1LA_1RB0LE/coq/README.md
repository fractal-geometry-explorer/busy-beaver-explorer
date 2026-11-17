# busycoq proof: 1RB---_1LC0RF_1LD0LC_0RE0LF_0RD1LA_1RB0LE halts iff 1RB0RA_0LC0RF_0LB1RD_1LE---_1RA0LF_1LE0RC halts

```coq
Theorem eqv: halts tm c0 <-> halts tm' c0.     (* TailWord.eqv, Eqv_TailWord.v *)
```

with `TM`, `halts` and `c0` from busycoq's `TM.v` and `Individual62.v`, `tm` the first machine and `tm'` the
second. `Print Assumptions TailWord.eqv` prints `Closed under the global context`. It decides neither machine: it
shows that they are one halting question. The same result is proved in Lean in `../lean/Lockstep.lean`
(`two_machines'`) and `../lean/RightEnd.lean`; this file is an independent proof with its own invariant.

## The argument

- `tm'` is `tm` read in a mirror with the states renamed by `g` (A→D, B→E, C→A, D→B, E→C, F→F); it starts in what
  is state C of `tm`.
- From blank tape, after 2 steps of `tm` and 49 of `tm'`, both are at the model's start `cfg0`: the same tape, except
  that `tm'` has the word `W8 = 10001101` once more beyond the rightmost visited cell q.
- A model configuration `Cfg` is read as a configuration of either machine (`to_config`). One model step `f` is a
  step of both, or the crossing of the far end when the head is in B on a 1 at q: 5 steps of `tm` (`far0`), 49 of
  `tm'` (`far1`).
- The invariant `P`: the abstraction of the model configuration (the four cells q-3..q, plus the state and head
  position when the head is among them) is one of the 28 entries of `S0`. `check_S0` (one `vm_compute`) shows that
  `S0` is closed under the abstract step and that no entry moves right from q except B on a 1.
- busycoq's `halts_iff` then gives `halts (machine b) c0 <-> iter_halts f cfg0` for both machines.

## Building

```sh
sh build.sh /path/to/busycoq      # a checkout of busycoq's BB6 branch
```

Tested with Coq 8.20.1 (busycoq's version; `build.log`) and Coq 8.18.0: about 3 s for this file. Changing `W8`, one
transition of `tm'`, or removing an entry of `S0` makes it fail. The file is also on the branch
`claude/project-thread-tinjly` of the fork fractal-geometry-explorer/busycoq, ready for a pull request to busycoq;
it has not been submitted there yet.

The explainers of both machines show each step in the browser (sections "One question, two machines" to "Checked in
Coq"); their engine is `../py/pair/pair.js`, tested against the numbers above by `node ../py/pair/test_pair.js`.
