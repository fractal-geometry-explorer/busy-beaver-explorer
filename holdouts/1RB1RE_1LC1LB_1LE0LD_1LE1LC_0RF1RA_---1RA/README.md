# 1RB1RE_1LC1LB_1LE0LD_1LE1LC_0RF1RA_---1RA

bbchallenge id 175628. One of the six-state holdouts whose halting from blank tape is open (group G07).
Family: **Collatz-like: 3/2 counter feeding a stack of slower counters (exact visit map on run lists)**. Decision: **open**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RE |
| B | 1LC | 1LB |
| C | 1LE | 0LD |
| D | 1LE | 1LC |
| E | 0RF | 1RA |
| F | --- | 1RA |

## What it does

Read the tape as runs of 1s separated by single 0s, left to right; `u` is a run of length 1 (cells `10`, a *unit*).
The right end of the tape never moves (it has been `... 4 u^3 4 1` since step 1.8·10^5); all the work is done by the
head near the **left** end. A **visit** is the moment B stands on the blank cell just left of the tape; the tape is
then a list of runs `l = [r0, r1, ..., rk]`.

### The visit map (exact, proved in Lean)

From one visit to the next the list changes as follows (`visit` in `py/visit.py` and in `lean/Visit.lean`):

1. `r0 += 2`.
2. Let `r_j` be the first odd run. **If there is none, the machine halts**: E runs over the whole tape (even runs
   keep it in phase) and F reads the 0 past the right end.
3. The odd run is joined with the run after it: `W = r_j + r_(j+1) + 2`. (If `r_j` is the last run it becomes
   `(r_j+1)/2` units followed by a run `W = 1` instead.)
4. A cascade then runs to the left, two runs at a time: the even run `2t` just left of the joined run crumbles into
   `t` units; the run before it takes two of them and grows by 4 (so the list reads `..., r+4, u^(t-2), W, ...`), and
   that grown run plus one becomes the next `W`, its even left neighbour crumbles, and so on.
5. The cascade ends at the left end in one of two ways: on the first run (`[r0+6, u^(t-2), W, ...]`, a **sweep** when
   `j = 2`), or with the first run itself crumbling, which leaves `[6, 4, u^(t-5), W, ...]` (a **conversion**).

On the domain D (all runs >= 1, no run of length 2, the first run even and either >= 12 or the list starting
`6, 4, 1, 1`) the map is proved for every list: `visit_step` in `lean/Visit.lean` says that the machine goes from the
visit with list `l` to the visit with list `visit l` (which is again in D), or halts when `visit l = none`. The run
from blank tape reaches the visit `l0 = [12, 1, 1, 1, 1, 1, 1, 1, 1, 1]` at step 423 (`blank_to_V`). Hence

    theorem halts_iff : HaltsFromBlank ↔ ∃ n, orbit n = none        -- orbit 0 = some l0, orbit (n+1) = visit (orbit n)

**The machine halts from blank tape iff the orbit of `[12, 1^9]` under the visit map reaches a list whose runs are
all even.** This is the exact Collatz-like condition; whether it ever happens is open. One invariant is easy (the
number of even runs stays odd) but does not exclude it.

### Epochs

Most visits are sweeps `[X, 4, u^(n+2), L] -> [X+6, 4, u^n, L]`. An **epoch** starts at `[6, 4, u^m, L]`, runs about
m/2 sweeps (X grows to about 3m), and ends with a conversion of the long run back into about 3m/2 units:

    m' = 3m/2 + d,    d in {-2, +1, +4} for m even,  d in {-1/2, +5/2} for m odd,

about 1.5 m^2 steps an epoch. The m sequence: 1, 4, 7, 10, 13, 22, 31, 49, 73, 109, 163, 244, 370, 553, 829, 1243,
1864, 2797, 4195, 6292, 9436, ... What happens between the last sweep and the conversion depends only on the parity of
m and on the first items of L, and changes those items: for m large the next stack L' is a function of L and of the
parity of m alone (`py/adversary.py` checks this at every node it expands).

**The list L is a stack of slower counters.** Its first item behaves like a smaller copy of the top level: a run r
followed by units grows by 6 and loses one unit per epoch of odd m (`18 u^8 -> 24 u^7 -> 30 u^6 -> 36 u^5 -> 42 u^4`),
and when its units run out it is itself converted into about r/2 units, eating from the item after it. Deeper items
change exponentially more rarely; the bottom of the stack freezes:

    step 1.8e5:   2 4 u^370  4 u^17 4 u^3 4 1
    step 1.1e8:   2 4 u^9436 9 u^25 4 u^4 4 u^3 4 1
    step 8.0e11:  2 4 u^816400 4 u^22 4 u^15 4 u^4 4 u^3 4 1
    step 7.3e29:  2 4 u^780830244113908 9 u^3 12 4 u^14 4 u^2 4 u^2 4 u^3 4^2 u^2 15 u^5 4 u^9 4^2 u^3 4 u^17 4 u^15 4 u^4 4 u^3 4 1

(sampled in state E at the left end, 30 steps before the visit `[6, 4, u^(m-2), L]`). A halt needs every run even,
in particular every unit of the stack gone: the whole stack must be used up.

### How far it was run

`py/runstack.py` is an exact simulator on run lists (every step of the machine, with the proved sweep applied in
bulk); it agrees with a cell-by-cell run at every visit of the first 3·10^6 steps and with `py/epochs.py` (an
independent macro simulator) at epoch 82 (step 731,635,044,147,616,129,664,614,609,127). With it:

- the visit map predicts all 5,405 visits of the first 3·10^7 steps (`py/visit.py check 3e7`);
- **100,000 epochs without a halt** (`py/visit.py epochs 100000`, one minute): the step count then has 116,996 bits
  (about 10^35219), the stack 113,485 runs. A longer run of the same program reached 260,000 epochs (step count of
  304,184 bits, about 10^91568) without a halt.
- In these 100,000 epochs the head passed 1 entry of the stack (an entry is a run with its repeat count) in 73% of the
  epochs, 2 in 22%, 3 in 4%, 4 in 0.27%, 5 in 0.04% and 6 twice: the depth reached falls off geometrically while the
  stack gains 0.28 entries an epoch. The stack size never came back more than 10 entries below an earlier value.

### Could some parity sequence empty the stack?

`py/adversary.py` follows both parities of m from every stack, starting from `4 u^17 4 u^3 4 1` (step 181,417):
breadth first to depth 19 (468,328 stacks), best first by size (60,000 expansions; smallest stack met `85 1 4 1`), and a sampled search to depth 40 (117,306 stacks: every one ends with an odd run, has at least 3 odd runs and no run of length 2).
No halt was found. The stack can be dug down to four runs (e.g. `N 1 4 1`, which then grows again), so there is no
simple "the bottom is never touched" invariant; the search is evidence, not a proof.

## Where it can halt

The halting transition is F0. A closed tape language from windows of 4 cells (`lean/EdgeCert.lean`, checked by
`decide` in `lean/Edge.lean`) shows that **it halts from blank tape exactly when F steps onto the blank region past
the right end of the tape** (`halts_iff_edge`). Since all the work happens at the left end, a halt needs the whole
stack L to be used up, a cascade that would have to reach the frozen bottom items.

## Status

Open (Collatz-like, with an exact reduced map).

- **Kernel:** `step_none_iff`, `blank_runs_kernel` (`lean/Blank.lean`); `sweep`, `convert` (`lean/Rules.lean`);
  `halts_iff_edge` (`lean/Edge.lean`); the eight moves of a visit (`lean/VisitRules.lean`, generated by
  `py/visit_rules.py`); `visit_step`, `blank_to_V`, **`halts_iff`**, `scan_none_iff` (`lean/Visit.lean`; axioms:
  propext, Quot.sound, and Classical.choice for the statement about all step counts).
  **native_decide:** `blank_runs_native` (10^7 steps).
- **Trusted computation:** no halt in 100,000 epochs (about 10^35219 steps; 260,000 epochs, about 10^91568 steps, in a
  longer run) with `py/runstack.py`, an exact simulator checked against direct simulation; the Python visit map
  against the machine at 5,405 visits.
- **Heuristic:** the depth the head reaches into the stack falls off geometrically while the stack grows linearly, so
  the probability of ever emptying it is tiny; no halt in the adversarial search over parities.
- **Open:** whether the orbit of `[12, 1^9]` under the visit map ever reaches a list with only even runs.

## Next steps

An invariant of the visit map that excludes "all runs even" would decide the machine. The parity count of even runs
is not enough, and the adversarial search shows that the stack can be dug almost to the bottom, so the invariant (if
there is one) must use the arithmetic of the runs, e.g. the last run staying odd (true in every stack of the sampled
search, not proved), not just the size of the stack.

## Remainder classes (family survey)

- **Rounds between end events, by remainder class** (trusted). Sample the run whenever the head is in state D reading 1 with only 0s to its left. Read rightwards from the head, the tape is then `A U^m B`: one long periodic block between two short context words. For each class (A, U, B, m modulo 1 or 2 (the smallest modulus that works for the context)) the next sample is simulated for six values of m and extended as an affine map of m (with a cubic step count). Along the direct run from blank tape to 3·10^9 steps (59 events) the class map predicts the next event in all 25 rounds it applies to. This is an extrapolation checked by computation, not a proof. Command: `python3 holdouts/1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---/py/ctxround.py 1RB1RE_1LC1LB_1LE0LD_1LE1LC_0RF1RA_---1RA L D 1 check 3e9`
- **1,742 rounds of the class map without a halt** (heuristic). Iterated with exact integers from the event at step 181,384 of the run (A = `(empty)`, U = `10`, m = 373, B = `1^4 (01)^18 1^3 (01)^4 1^3 01`): 1,742 rounds without meeting a halting class; m then has 519 bits (about 10^312 steps of the machine). 1,742 distinct contexts occur, the longest of 2,729 cells. Command: `python3 holdouts/1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---/py/ctxround.py 1RB1RE_1LC1LB_1LE0LD_1LE1LC_0RF1RA_---1RA L D 1 orbit 1742`
- **No halting class among 5,000 contexts** (heuristic). Breadth first from the starting context, with every remainder at every context (whether or not the numbers can really produce that sequence of remainders, and only for m large compared with the contexts): 5,000 contexts expanded, 6,526 found, to depth 23. None of them halts; the search is not complete (the set of contexts keeps growing), and it says nothing about a halt that needs a context as long as the block itself. Command: `python3 holdouts/1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---/py/ctxround.py 1RB1RE_1LC1LB_1LE0LD_1LE1LC_0RF1RA_---1RA L D 1 bfs 5000`

## Pages

- [`pages/holdouts/1RB1RE_1LC1LB_1LE0LD_1LE1LC_0RF1RA_---1RA/explainer.html`](../../pages/holdouts/1RB1RE_1LC1LB_1LE0LD_1LE1LC_0RF1RA_---1RA/explainer.html)
- [`pages/holdouts/1RB1RE_1LC1LB_1LE0LD_1LE1LC_0RF1RA_---1RA/proof-status.html`](../../pages/holdouts/1RB1RE_1LC1LB_1LE0LD_1LE1LC_0RF1RA_---1RA/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RE_1LC1LB_1LE0LD_1LE1LC_0RF1RA_---1RA/lean/check.sh
cd holdouts/1RB1RE_1LC1LB_1LE0LD_1LE1LC_0RF1RA_---1RA
python3 py/rules.py | diff - lean/Rules.lean
python3 py/visit_rules.py | diff - lean/VisitRules.lean
(cd ../../tools/py && python3 -m bbtools.ctl 1RB1RE_1LC1LB_1LE0LD_1LE1LC_0RF1RA_---1RA 4 lean H175628 Blank) | diff - lean/EdgeCert.lean
python3 py/visit.py check 3e7          # the visit map (both forms) against the machine at 5,405 visits, 1 min
python3 py/visit.py epochs 100000      # 100,000 epochs, no halt; depth statistics, 1 min
python3 py/adversary.py bfs 19         # both parities from every stack, a few minutes
python3 py/adversary.py sample 40 2000
python3 py/epochs.py 1RB1RE_1LC1LB_1LE0LD_1LE1LC_0RF1RA_---1RA 2 1e30 E L "pre:2 4 1^"     # epoch starts, ~1 min
```
