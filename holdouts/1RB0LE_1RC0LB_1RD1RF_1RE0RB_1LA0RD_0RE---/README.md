# 1RB0LE_1RC0LB_1RD1RF_1RE0RB_1LA0RD_0RE---

bbchallenge id 3006, a six-state holdout of group G05 (growth class fixed/sqrt). **Open.** The generic sweep rules
are proved in Lean (kernel). An exact macro simulator, checked against the machine, runs 2.96·10^13 steps without a halt.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LE |
| B | 1RC | 0LB |
| C | 1RD | 1RF |
| D | 1RE | 0RB |
| E | 1LA | 0RD |
| F | 0RE | --- |

## What it does

**E-records.** Sample the run whenever the head is in state E on a new rightmost cell (reading 0) with a 1 just
left of it. The tape is then always

    <n0> s1 <n1> s2 ... sk <nk> 1 E>0        <n> = (10)^n,  s = S (= 01100), 0 or 1

The *defect* is the last separator that is not `S`. The *zone* is the blocks after it: `y` first, `z` last, `m` blocks.
One E-record leads to the next, and `c/erec.c` prints every one of them.

**One sweep** (the signals, all in `lean/Gadgets.lean`):
- The head writes a 1 and a leftward signal `A>1` starts.
- Crossing `<n>` costs 2n steps (`across`). Crossing `S` costs 21 steps and leaves `(10)^2 1` (`sgad`). So the zone
  is carried, as `(10)^(y+2) 1 (10)^(w1+2) 1 ... (10)^z 1`, to the defect.
- At the defect the signal turns:
  - defect `1`: 2Y + 4 steps (`turn1`);
  - defect `0` after a block x ≥ 2: 2Y + 16 steps (`turn0`).
- D then runs right. Each `(10)^(w+2) 1` becomes `S (10)^w` (`dunit`). At the blank end D writes the 1 of the next
  record, so the tape is 2 cells longer.

The resulting **generic rules** (`lean/Macro.lean`, for any zone and any tape left of the defect):

    m >= 2:  ... 1 y S w.. S z+2   ->  ... 0 y+3 S w.. S z          4z+4y+40+Σ(4w+26) steps   record_d1
             ... x+2 0 y S w.. S z+2 -> ... x 1 y+5 S w.. S z       12 steps more              record_d0
    m = 1:   ... 1 z  -> ... 0 z+1   (4z+6)        ... x+2 0 z -> ... x 1 z+3   (4z+18)        record1_d1/_d0

About 80% of sweeps follow these rules (9,921 of the 12,434 in the first 2·10^8 steps). The rest are **events**,
all found by symbolic runs and checked against the machine:
- z = 1: the S and the 1 merge into the previous block (+2).
- z = 0: the last S becomes the new defect, ending `0 <2>`, and the old defect freezes.
- `S 1 0 y` → `0 0 1 y+6`.
- `a 0 0 0 y` → `a-1 1 2 S y`.
- `a S 0 0 y` → `a 0 6 S y`.
- `a 0 1 0 y` → `a+y+5`: the defect vanishes.
- At the left edge with no defect, `<2> S` is prepended at every record.
- A frozen 1 met with x = 0 merges blocks and the turn passes on to the next defect to the left.

**Long-run behaviour.** The blocks settle on the values 4^k − 2 (2, 14, 62, 254, ..., 1048574). A block grows
n → 4n + 6 as the defect passes it. So the tape acts as a counter whose digits are runs of equal blocks, and the left
edge grows in bursts of `<2>` blocks. Two snapshots:
- at 2·10^8 steps: about 1,970 × `<2>`, then 137 × `<14>`, then `62 303 853 2150 1118`;
- at 2.96·10^13 steps: 244,161 blocks with one defect, ending `S 1048574 S 1048574 S 491400`.

**Where it could halt.** Only F reads a 1 to halt, which needs `D>1 0 1 1`. Inside a sweep that means a turn with
the first right block Y ≤ 1:
- in a zone of two or more blocks, Y = y + 2 ≥ 2, so the generic rules cannot halt;
- in a zone of one block, Y = z, and z only comes back as 2 after an event and then grows.

None of the 891 window rules met in the long run halts.

## Status and evidence

**Lean, kernel only** (`lean/Gadgets.lean`, written by `py/gen_gadgets.py` with `bbtools.symtm.prove`): `sgad`,
`turn1`, `turn0`, `dunit`.

**Lean, kernel only** (`lean/Macro.lean`):
- the encodings `blk`, `sS`, `sl`, `rd`, `zone` and `erec`;
- `across`; `apass` (the leftward pass over any number of `S w`); `dpass` (the rightward pass);
- `to_turn` and `from_turn`;
- **`record_d1`, `record_d0`, `record1_d1`, `record1_d0`** (the generic sweeps, exact step counts) and `rcost_eq`
  (the closed form);
- `fsteps431` and `reach431`: blank tape reaches `<2>S<2>S<2>S 1 <5> 1 E>0` at step 431. `reach457` is the next
  record by `record1_d1`.

**Lean, native_decide**: `blank_runs_native`, no halt in 10^7 steps (`lean/Blank.lean`).

**Computed (trusted)**:
- `py/mac15b.py` is the macro simulator. Each sweep is a symbolic run (`py/symrec.py`) on a window: the defect
  region and the last block exactly, the middle zone abstracted, extra steps 26 per collapsed block plus 4 per
  cell. Rules are cached, and two-record events are fused.
- It matches the whole tape and step count at every E-record of the first 2·10^8 steps
  (12,384 compared from its start record at step 3513; `py/cmpm.py`, against `c/erec.c`), and at the sampled records to 4.09·10^9 steps (`py/verify_e27k.py`).
- `py/mac15c.py` is a run-length version; `py/test15c.py` checks it against 12,014 records, with 0 mismatches.
- `py/long15.py` (mac15b with linear jumps): 5,692,991 sweeps, 2.9654·10^13 steps, no halt. It was stopped at
  that point by the time limit, not by a halt.

**Heuristic**: the halting argument above, and the counter picture. Neither is proved.

**Open**: whether it halts. The events are not in Lean, and no closed language of macro configurations is known.

## Reproduce

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LE_1RC0LB_1RD1RF_1RE0RB_1LA0RD_0RE---/lean/check.sh
python3 holdouts/1RB0LE_1RC0LB_1RD1RF_1RE0RB_1LA0RD_0RE---/py/gen_gadgets.py     # rewrites lean/Gadgets.lean
gcc -O2 -o erec holdouts/1RB0LE_1RC0LB_1RD1RF_1RE0RB_1LA0RD_0RE---/c/erec.c
./erec 1RB0LE_1RC0LB_1RD1RF_1RE0RB_1LA0RD_0RE--- 200000000 > e2e8.txt          # every E-record
cd holdouts/1RB0LE_1RC0LB_1RD1RF_1RE0RB_1LA0RD_0RE---/py
python3 mac15b.py 12400 m.txt && python3 cmpm.py ../../../e2e8.txt m.txt   # macro vs machine: compared 12384 bad 0
python3 test15c.py ../../../e2e8.txt
python3 long15.py 3e13 long15.log                               # hours
```

## Layout

| path | what it is |
|---|---|
| `lean/Machine.lean`, `lean/Blank.lean` | the machine and bounded runs (generated) |
| `lean/Gadgets.lean` | cell gadgets (generated by `py/gen_gadgets.py`) |
| `lean/Macro.lean` | encodings, passes, the generic sweep rules, the reach from blank tape |
| `c/erec.c` | direct simulator printing every E-record |
| `py/symrec.py` | one sweep, run symbolically on a macro configuration |
| `py/mac15b.py`, `py/mac15c.py` | macro simulators (flat and run-length) |
| `py/cmpm.py`, `py/test15c.py`, `py/verify_e27k.py` | checks against `c/erec.c` output |
| `py/long15.py` | the long run |

## For later

- **Events in Lean.** Prove the event rules with `symtm.prove`. They are short runs on windows of a few blocks.
- **A full macro step.** Define `mstep` over the list form and prove it sound, as in the worked example. The
  run-length form `mac15c.py` is the natural state space.
- **A non-halting proof.** Find an invariant on macro configurations that the events keep and that excludes a
  halting turn: a zone of one block with z ≤ 1 at a turn, or a frozen-defect turn with a right block ≤ 1. Candidates
  are block values ≡ 2 mod 4 away from the zone, and a single non-S separator after the first long run.
- **A faster simulator.** Speeding the run up further needs level-2 acceleration: detect cycles in the run-length
  snapshots when the defect passes a run of equal blocks `4^k − 2`.
