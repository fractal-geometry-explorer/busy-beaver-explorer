# busycoq proofs: two BB(6) holdouts halt

Coq proofs, on [busycoq](https://github.com/ccz181078/busycoq) (branch BB6), that two BB(6) holdouts halt from
blank tape:

| machine | bbchallenge id | final theorem |
|---|---|---|
| `1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA1RB_1RE---` | 60498 | `halts : halts tm c0` in `M_1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA1RB_1REHHH.v` |
| `1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA0RE_1RE---` | 32161 | `halts : halts tm c0` in `M_1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA0RE_1REHHH.v` |

`TM`, `halts` and `c0` are busycoq's (`TM.v`, `BB62.v`, `Individual62.v`). `Print Assumptions halts` prints
`Closed under the global context` for both: no axioms, no `Admitted`.

## The proof

Both machines obey the visit law described in `holdouts/1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA1RB_1RE---/README.md`
("It halts"): a visit rewrites the stream to its right by `0 x -> 1 x`, `100 x -> 000 v(x)`, `110 x -> 000 v(x)`,
`1010 x -> 1010 v(v(x))`, and a visit that meets `1011` halts. A round puts `1 0` in front of the stream and
makes one visit. The machine halts in round 161,211.

- `VisitLaw2.v` is the checker of busycoq pull request 59 (three other machines with the same law), with two
  changes. The visit law is a parameter, so that the file does not depend on a machine. And a visit may have two
  forms, V and W: the two visits behind a `1010` are W, then V, and the rule for `110` is only asked of form V.
  The checker keeps form W away from `110`: its exact scan rejects a word in which the cells behind a `1010`
  start with `11`, and the proof shows that this is enough (`okW`, `VS`). `check_ok : check 161210 = true` is one
  `vm_compute` of about 15 minutes: 161,210 rounds, then a round that meets `1011`.
- Each machine file proves the rules for its own table by running the machine (form V is "state C on the cell
  before the stream", form W is the same in state F) and applies `halts_of_check`.

In 60498 form W also obeys the rule for `110`. In 32161 it does not (`1100 x -> 1010 v(x)` instead), so that
machine needs the two-form law. The Lean proof (`lean/Halt.lean` of each machine) uses the same law with the
same guard, and a different checker.

## Checking

Coq 8.20.1, busycoq BB6 at commit 33209bc. Copy the three files into busycoq's `verify/`, build busycoq's core
there, then

    coqc -Q . BusyCoq VisitLaw2.v
    coqc -Q . BusyCoq M_1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA1RB_1REHHH.v
    coqc -Q . BusyCoq M_1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA0RE_1REHHH.v

`build.log` is the output of these commands, with times.
