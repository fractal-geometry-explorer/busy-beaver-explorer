# busycoq templates vs the holdouts

Tools for [`holdouts/BUSYCOQ_TEMPLATES.md`](../../holdouts/BUSYCOQ_TEMPLATES.md):

| file | what it does |
|---|---|
| `carry.c` | every carry rule `E D1^n <{{Q}} M -->+ F D0^n <* M' {{Q'}}>` (n = 0..6) of each machine on stdin, both sides (right side via the mirror; printed words are tape order, Coq list order is reversed) |
| `carryuse.c` | `./carryuse STEPS < carry rules`: how often each rule's start pattern occurs in the run from blank tape, and the largest n |
| `classify.py` | sorts machines by the rules their runs use (two linked counters, counters on both sides, one counter, none) |
| `near.py` | proved machines in busycoq `verify/*.v` within 2 transitions of each holdout, as written or mirrored |
| `transplant.py` | one copy of the template file per (holdout, neighbour) with the holdout put in; compile in `verify/` |
| `trim.py` | drops the other machines' proofs from a copy, to keep compile times down |
| `probe.py` | for `SOC_2_x` copies whose `es` leaves goals open: rewrites the proof to report rule by rule what is proved |
