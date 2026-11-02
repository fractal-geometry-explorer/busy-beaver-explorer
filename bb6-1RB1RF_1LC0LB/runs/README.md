# Long runs

| file | command | CPU time |
|---|---|---|
| `growth_1e10.txt` | `c/growth.c MACHINE 10000000000`: width, ones and left-end extensions at steps 10, 20, 50, ... | 1 min |
| `left_1e10.txt` | `tools/c/tokrun MACHINE 10000000000 a=10,b=110 L 100000`: the tape as words at the 207 left-end moments | 1 min |

`py/replay.py` reads `left_1e10.txt`. MACHINE is `1RB1RF_1LC0LB_1RE0LD_1LB0RF_0RA0RC_1RE---`. See
`notes/LAB_NOTES.md` (2 November 2026).
