Outputs of long runs (see ../notes/LAB_NOTES.md for how each was made).

- `left_records_1e10.txt`: every step up to 10¹⁰ at which the head reaches a cell left of all earlier ones, with the
  tape (lines cut at 200 characters), and the final line of the run:
  `tools/c/tmrun 1RB1RA_1RC1LB_1LD0RA_---0LE_1LC0LF_1RE0LB 10000000000 records 100000000 | awk '$2=="L" || /running|halted/ {print substr($0,1,200)}'`
  (about a minute).
- `left_arrivals_macro.txt`: the arrivals of the wave at new tape on the left, from the block model in C, up to
  7·10¹⁰ macro steps (3.7·10²² machine steps): `gcc -O2 -o blkrun c/blkrun.c && ./blkrun 200000000000 10000000000`
  (stopped after 7·10¹⁰; about 25 minutes).
- `superrun_long.txt`: the super orbit with the last 44 blocks tabulated, to 6·10²³ super steps (2.7·10⁴⁹ machine
  steps): every return to the left end, every level added to the table, and exact status lines:
  `gcc -O3 -march=native -o superrun c/superrun.c -lm && ./superrun -E 270000000 -q 300` (one core, 8 GB; stopped
  after 40 minutes when it ran out of memory).
- `superrun_checkpoints.txt`: the whole tape every 10⁷ super steps up to 10⁹, with its machine step:
  `./superrun -S 1000000000 -c FILE 10000000` (about 30 s); for checking the orbit in chunks.
- `odds.txt`: `python3 py/top_stats.py odds`: the returns of `superrun_long.txt`, the floor for the next return's d₁
  (2^79.96, from `lean/Monotone.lean` and the top blocks of the last status line) and the corrected odds of a halt.
- `toppass_1e17.txt`: `python3 py/top_stats.py toppass 1e17` (about 30 s): how often a wave that reaches the k-th
  block from the left passes it, on the orbit from blank tape.
- `bottom2adic_18.txt`: N mod 2¹⁸ over one exact period of the last 18 blocks, from the tape at super step 10⁹:
  `gcc -O2 -o bottom2adic c/bottom2adic.c -lm && ./bottom2adic 18 1000000000 1048576000 $(tail -1 superrun_checkpoints.txt | awk '{for(i=NF;i>2;i--) printf "%s ",$i}')` (25 s).
- `ensemble_summary.txt`: `python3 py/top_stats.py ensemble` on 60,000 orbits of `c/ensemble.c`
  (`./ensemble 10000 16777216 SEED 2 4 100 ID` for seeds 100 to 102, and 60000 per seed for 200 to 203, stopped after
  about 7,500 each; the raw output, 20 MB, is not kept).
