# 1RB1LF_0RC0RB_0LD1RB_1LE0LB_0LA1LC_0LB---

bbchallenge id 57056, group G12. One of the six-state holdouts whose halting from blank tape is open. Family: two
binary counters fed by alternating ticks, with borrows moving words between two runs (exp/exp; phase changes not
modelled).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LF |
| B | 0RC | 0RB |
| C | 0LD | 1RB |
| D | 1LE | 0LB |
| E | 0LA | 1LC |
| F | 0LB | --- |

## What it does

Words: a = `1100`, b = `110`, c = `10` (read longest first). Each time the head is in F on the leftmost visited
cell (a *left-end visit*), the tape right of it reads

    F>0  c^s  H  X_1 bb X_2 bb ... bb X_w  b^m  cc0  b^j

* `c^s` is the **left counter**, here at 0. Its digits are four cells, `1010` = 0 and `1000` = 1, least significant
  on the right, followed by `1 0`; the head comes back to it in E on the 0 after that `1`. Lean proves both of its
  rules for every length n and every tape L, R around it (`lean/Counter.lean`):
  * `incr`: `L 1010 (1000)^n 1 E>0 R` → `L 1000 (1010)^n 1 0 C> R` in 10n + 7 steps;
  * `overflow`: `0^inf (1000)^n 1 E>0 R` → `0^inf (1010)^(n+1) 1 0 C> R` in 10n + 13 steps (the head visits a new
    cell on the left in state F: this is the left-end visit).
* H is a short header: `ab` most of the time, `ababcc` or `abccbcc` after a phase change.
* `X_1 .. X_w` is the **right counter**: digit a = 1, cc = 0, X_1 least significant; v its value.
* `b^m` and `b^j` are two **piles** of b, separated by the marker `cc0`. Nothing is written right of `b^j`.

**A round** runs from one left-end visit to the next. The left counter runs through all its 2^(s/2) values; between
two of its increments the head goes right once and decrements the right counter; each borrow of the right counter
(0 → 2^w − 1) moves one b from the first pile to the second; at the end the left counter overflows and is one digit
longer. In the round from step 4,982 to 7,434 (s = 10) the head turns 64 times at the low end of the left counter:
32 increments (turn counts 32, 16, 8, 4, 2 at its digits) and 32 trips to the right counter (3 digits, 4 borrows).

**Round law.** With D = 2^(s/2) and t = (D − v − 1) div 2^w + 1 (the borrows of D decrements from v):

    m ≥ t (and m > t if H ≠ ab):   (s, H, v, m, j)  →  (s + 2, H, v − D mod 2^w, m − t, j + t)

All 39 regular rounds from step 1,756 to 10^10 follow it exactly (`py/round_law.py`, output
`py/round_law_1e10.txt`). Within a phase D is a multiple of 2^w, so v stays and t doubles each round: this is the
doubling map (m, j) → (m − j − k, 2j + k) found before (`py/phase_check.py`, k = t − j).

**Phase changes.** When m < t the round ends differently (24 times up to 10^10 steps). From H = `ab` the left
counter comes back two digits shorter (s − 4) and the header becomes `ababcc` or `abccbcc` (four times it stays `ab`,
with m + j growing by 4); from those headers the next visit has s + 2, header `ab`, w + 1 digits and m + j + 1. The
new digits X and the new piles are not yet predicted. Example: (s, H, X, m, j) = (36, ab, 1111111101100, 5, 29) at
step 72,347,964 → (32, ababcc, 1111110010001, 31, 4) at step 77,767,580.

## Status

**Decided outside: it never halts.** Busycoq pull request 103 (Alex Havrilla of DeepMind) proves it in Rocq, compiled here with Coq 8.20.1 and no axioms. It reads the left counter in bijective base 2 and proves a 16-shape invariant in which each pass brings at least as many carries into the counter as its value (the calls double across each block `1010100100`), enough to erase every defect, so the undefined macro steps that lead to F reading a 1 never occur.

This repository on its own: proved in Lean, kernel only: the halting configurations (`step_none_iff`), no halt in 10,000 steps, the two
rules of the left counter (`incr`, `overflow`, `lean/Counter.lean`). Proved with `native_decide`: no halt in 10^7
steps. Computed (trusted): no halt in 10^10 steps; the round law on all 39 regular rounds to 10^10; a closed tape
language of 5-cell windows confines a halt to `F>1 1 1 0 1 0`.

## How far it was run

Direct simulation (`tools/c/tmrun.c`) to 10^10 steps (68 left-end visits, 39 regular rounds, 24 phase changes; at
step 6,779,924,480 the configuration is s = 46, w = 19, v = 444116, m = 38, j = 12, H = `ab`). The round law alone
takes the run one round further, to s = 48, m = 22, j = 28 (t = 16); the round after needs t = 32 > m and is a phase
change. There is no
accelerated run past phase changes, since their rule is missing and each round costs about 2^(s/2) ticks.

## Open questions

* The phase-change map: the new right-counter digits and piles from (s, H, X, m, j) when m < t. A fit
  v' = 2^w + 3 − r mod 2^(w+1), with r the decrements left after the failed borrow, matches three of the seven
  `ababcc`/`abccbcc` → `ab` changes, is off by one in three and does not apply to the seventh (there m = t), so the
  rule is close to but not that.
* With that map, a `halts_iff` reduction to an arithmetic system in (s, H, v, w, m, j) and a run over many phases.
* Whether a phase change can ever produce `F>1 1 1 0 1 0` (the only possible halt).

## Layout

| path | what it is |
|---|---|
| `lean/Machine.lean`, `lean/Blank.lean` | the machine, the halting configurations and bounded runs (generated) |
| `lean/Counter.lean` | the increment and overflow rules of the left counter (generated by `py/gen_counter.py`) |
| `py/round_law.py`, `py/round_law_1e10.txt` | the round law checked at every left-end visit to 10^10 steps, and the phase changes |
| `py/phase_check.py`, `py/phase_check_5e9.txt` | the earlier check of the doubling map (m, j) → (m − j − k, 2j + k) |

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1LF_0RC0RB_0LD1RB_1LE0LB_0LA1LC_0LB---/lean/check.sh
gcc -O2 -o /tmp/tmrun tools/c/tmrun.c && /tmp/tmrun 1RB1LF_0RC0RB_0LD1RB_1LE0LB_0LA1LC_0LB--- 10000000000 at F L 5000 > fl.txt
python3 holdouts/1RB1LF_0RC0RB_0LD1RB_1LE0LB_0LA1LC_0LB---/py/round_law.py fl.txt
cd tools/py && python3 -m bbtools.ctl 1RB1LF_0RC0RB_0LD1RB_1LE0LB_0LA1LC_0LB--- 5
```

## Pages

- [`pages/holdouts/1RB1LF_0RC0RB_0LD1RB_1LE0LB_0LA1LC_0LB---/explainer.html`](../../pages/holdouts/1RB1LF_0RC0RB_0LD1RB_1LE0LB_0LA1LC_0LB---/explainer.html)
- [`pages/holdouts/1RB1LF_0RC0RB_0LD1RB_1LE0LB_0LA1LC_0LB---/proof-status.html`](../../pages/holdouts/1RB1LF_0RC0RB_0LD1RB_1LE0LB_0LA1LC_0LB---/proof-status.html)
