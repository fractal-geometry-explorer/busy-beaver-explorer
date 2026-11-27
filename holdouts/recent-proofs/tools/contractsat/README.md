# contractsat

Search for a contract table (classes of half tapes, what each trip returns and leaves behind) with a SAT solver.
Write-up: [`../../followup/contract-sat.md`](../../followup/contract-sat.md). Needs `pip install python-sat`.

| file | what it is |
|---|---|
| `contractsat.py` | the encoder and the lazy loop; `--runs b,Z,D` for run-length structured classes, `--keys` to restrict the window graph to a real run |
| `check.py` | independent checker for a certificate written with `--out` |
| `keys.c` | window situations of a real run, input for `--keys` |
| `screen.py` | runs a list of (machine, direction) pairs |
| `screen-n8-w12.tsv` | all 1,002 directions of the 501 open holdouts, 8 classes, window 12: machine, direction, n, W, result, window situations encoded, seconds |
| `targets.sh`, `targets-structured.txt` | structured classes on the four target machines |
| `sanity.py`, `controls.py`, `controls-4state.txt` | random small machines: every table found passes `check.py` |
| `lr_run.py`, `keys_24.txt`, `keys_32.txt` | wrapper and inputs of the two longrun jobs on 1RB0LD_1LC0RE_---1LD_1LE1LA_1RA0LF_1LC1RE |
