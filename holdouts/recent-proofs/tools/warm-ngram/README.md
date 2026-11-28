# warm-ngram: busycoq's history n-gram, CPS_LRU and RWL_mod deciders with late starts

Tools for [`../../followup/warm-history-ngram.md`](../../followup/warm-history-ngram.md) (busycoq PR #121).

| file | what it is |
|---|---|
| `wng.cpp` | busycoq's `CTL_NG_QSym` (n-gram CTL with tape histories) with the warm start of PR #121; `-c` gives busycoq's own `NG` behaviour |
| `wblk.cpp` | busycoq's `CPS_LRU` and `RWL_mod` (CTL on the block machine) with any start time |
| `screen.py`, `open501.txt` | the 90-setting screen of the 501 open holdouts (a `longrun` job, one shard per core) |
| `screen-501-nov28.tsv.gz` | its 45,090 results |
| `sametable.py`, `sametable-501-nov28.txt` | open holdouts whose table appears in a busycoq file with another start state |
| `sibling-params.txt`, `sibling-jobs.txt`, `sibrun.sh`, `sibling-runs-nov28.txt` | the siblings' busycoq parameters and the runs of their deciders on the holdouts |

```sh
g++ -O2 -std=c++17 -o wng wng.cpp && g++ -O2 -std=c++17 -o wblk wblk.cpp
./wng 1RB0RC_1LC0RB_1LD0LD_1RA1LE_---0LF_1LB1LF 30000 3 12 2 0                       # NONHALT 14630 ...
./wblk 1RB0RC_1RC1RE_0RD1RF_1LD1LB_---0LD_0LA1RA CPS 1001 6 3200 0 2 0 0 -S 10000     # busycoq nonhalt53731: NONHALT
python3 sametable.py <busycoq>/verify open501.txt > sametable.txt
```

Checks: `wng` agrees with 40 random lemmas of busycoq's `NG_v1.v`; `wblk` reproduces the 19 `CPS_LRU` / `RWL_mod`
sibling proofs listed in `sibling-params.txt`. These are search tools; only the Rocq proof itself is a proof.
