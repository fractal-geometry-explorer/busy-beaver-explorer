# Collatz-like holdouts (family R15)

The 98 machines that `holdouts/FAMILIES.md` parks as "Collatz-like maps and cryptids", triaged on 21 November 2026.

| file | what |
|---|---|
| `triage.json` | one record per machine: tier, outlook, map, halting condition, what Lean proves, how far it was checked, odds, next step, bucket |
| `hunts.json` | the halt-hunt runs made for the triage |
| `maps.js` | 20 of the maps as BigInt steppers (used by the page) |
| `test_maps.js` | checks `maps.js` against the machines: `node tools/collatz/test_maps.js` |
| `c/amap.c`, `c/dm9516.c` | the two new long-run programs (A(a, b) rules of 1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC; DeepMind's map of 1RB0LE_1LC1RA_1RA1LD_0LC0LA_0RE1RF_0RC---) |
| `build.py` | writes `TRIAGE.md` and `pages/holdouts/collatz-family.html`; `--check` tests they are current |

```sh
python3 tools/collatz/build.py
node tools/collatz/test_maps.js            # about 10 minutes
gcc -O2 -o amap tools/collatz/c/amap.c -lm && ./amap 1e12
gcc -O2 -o dm9516 tools/collatz/c/dm9516.c && ./dm9516 1e12 0
```
