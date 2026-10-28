# Differential test of the simulators

`check.sh` runs every simulator that current work uses on the same random well-formed round starts as the proved
mark model, and compares them round by round:

| name | program |
|---|---|
| oracle | `Oracle.lean`: `roundZ` from `../lean/BB6/Round.lean`, proved to follow the machine |
| `endgame`, `exit`, `tree` | the round function of `../cert/check_*.py` (`pysim.py`) |
| `nrefdfs2`, `lined`, `rtree3d`, `rtree3e`, `gx3` | the C engines in `../csearch/`, through `drv_q.c`, `drv_f.c`, `drv_gx.c` |
| `br`, `brf` | the blank-tape run's engines `../blankrun/engine.h` and `fast.h`, through `drv_br.c`, `drv_brf.c` |
| `stepper` | `../stepper/engine.js` (`stepper.js`) |
| `machine` | the bare transition table (`stepper.js NR machine`) |

Where the oracle and a program both make a claim (the next round start, or a halt) they must agree. "Uncovered" makes
no claim. The report also counts the rounds a program claims where the oracle claims nothing. Those rounds are not
checked.

```sh
cd ../lean && ./check.sh                    # builds out/, which Oracle.lean imports
cd ../simtest && ./check.sh 20000 1 12      # starts, seed, rounds
python3 run.py --canon 3000 1 8 name="cmd"  # --canon: count only different tapes, not a trailing wall
ORACLE="node stepper.js 12 machine" python3 run.py ...   # the bare machine as the reference
```
