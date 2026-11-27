# patcount: counter programs made from pattern counts

Technique C of `holdouts/recent-proofs/technique-brainstorm-2-nov27.md`. Results and conclusions:
`holdouts/recent-proofs/followup/pattern-counts.md`.

## The counter program

A tape is described by the head state, an exact window of radius R around the head, and two vectors of numbers:
for each n-cell pattern, how often it occurs left of the window and right of it (occurrences that start at or
before the last non-zero cell; optionally separated by start position mod m). One machine step shifts the window.
The pattern that leaves the window on one side is added to that side's vector. On the other side one pattern is
removed and its last cell enters the window. Which pattern is removed is not known, so every candidate is tried
whose count is positive and for which the remaining counts can still be the pattern counts of a half tape (degree
balance and connectedness of the n-gram graph: the conditions for an Euler trail). This is the best step function
there is for this description: a successor is produced exactly when some tape with these counts makes that step.

## Files

| file | what it does |
|---|---|
| `patcount.cpp` | explores the counter program with every count remembered exactly up to K and as "big" above. `patcount TM n m K [maxstates] [certfile]`; environment: `RAD` (window radius, default n-1), `START=T` (start from the real configuration after T steps instead of the blank tape), `CHECK=T` (after `SAFE`, test that the first T real configurations are in the explored set), `TRACE=1` (print the path to the halt), `NODROP=1` (search for halting paths only: big-1 stays big). Prints `SAFE` (the explored set is closed and has no halting state: with `certfile` it is written out), `HALT` (a halting state is reached; `path_exact=yes` means no count on the path reached the cap, so the path exists in the program without a cap), or `LIMIT` |
| `shuffle_test.py` | the rearrangement test. Takes real configurations at random times, rearranges each half tape beyond the window without changing any pattern count (a random or adversarial Euler trail), and runs the machine from the result. With `--iter N` it repeats this N times per configuration with random numbers of steps in between, which samples the states the counter program reaches from late real configurations. A halt refutes the vocabulary for that machine: no invariant in these counts, found by any solver, can exclude the halt. No halt proves nothing. Vocabularies: `cells:n` (n-grams of cells), `d1:n`, `d0:n` (n-grams of unary digits `1^d 0` or `0^z 1`), `runs:n` (n-grams of runs) |
| `tmrun.cpp` | plain simulator used by `shuffle_test.py` |
| `realtrace.py` | the real run in the output format of `TRACE=1`, to find where a halting path leaves the real run |
| `screen.sh`, `shufscreen.sh` | run `patcount` or `shuffle_test.py` over a list of machines; one line per result, resumable |
| `summarize.py` | table of halted chains per machine from `shuffle_test.py --iter` output |
| `controls.txt`, `targets_f08.txt`, `targets_r08.txt`, `open_all.txt` | machine lists |
| `results/` | the outputs quoted in the note |

Build: `g++ -O2 -o patcount patcount.cpp && g++ -O2 -o tmrun tmrun.cpp`.

## Checks on the tool

- `CHECK`: on machines where the result is `SAFE`, the abstraction of each of the first 30,000 real configurations is
  in the explored set (4 small machines, 4 settings each, no miss).
- A `HALT` path with `path_exact=yes` was compared with the real run (`realtrace.py`): it follows the real run and
  leaves it at a step where two tapes with the same counts differ.
- No holdout got `SAFE`, so no certificate was written and nothing rests on the tool being sound.
