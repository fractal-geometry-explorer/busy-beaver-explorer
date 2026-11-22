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

### What a halt needs, exactly

Two facts about the map, the first read off its definition, the second checked by enumeration:

- **The map only touches the list up to the run after the first odd run;** everything after it is copied. The last
  run of the orbit is 1 (odd) from the start. It can change only at a visit where the first odd run is the last run
  (then it becomes `W = 1` again, odd) or the last but one (then `W = r_j + r_last + 2` is even if `r_last` is odd).
  So **a halt needs a visit at which every run except the last two is even** (after `r0 += 2`): the cascade must
  have worked through the whole stack down to its bottom.
- **One and two visits before a halt** (`py/last_step.py`, all 1,628,875 lists of D with at most 6 runs, each at most
  13, first run up to 22): `visit l` has only even runs exactly when `l = [X, 1]` or
  `l = [X, 4, odd, odd, even, ..., even]`; the only lists of D mapped to `[X, 1]` are `[X-6, 3]`, and none is mapped
  to `[X, 3]`. So (as far as these bounds reach) `[X, 1]` cannot occur in the orbit of `[12, 1^9]`, and a halt needs a
  visit with the list `[X, 4, odd, odd, even, ..., even]`. (An enumeration on small lists, not a proof for all lists.)

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
No halt was found within those depths. The stack can be dug down to four runs (e.g. `N 1 4 1`, which then grows
again), so there is no simple "the bottom is never touched" invariant.

**Yes, some parity sequence does** (`py/halting_twin.py`, 22 Nov 2026). From that stack, 247 odd epochs in a row
empty it (each odd epoch takes one unit from the first counter; when the units run out the counter converts and
refills from the next item: `4 u^17 4 u^3 4 1 -> 106 4 u^3 4 1 -> 4 u^55 4 1 4 1 -> ... -> 1030 1 -> 1036`) and one
even epoch then halts. The word is longer than the searches above reached. Since `m' = (3m + c)/2` with `c` fixed by
the stack and the parity, the word pins `m` mod 2^248:

    m0 = 41155288665286261693662459474261276833979426164594950575389163897113542655   (mod 2^248)

and the exact run-stack simulator from the list `[6, 4, u^m0, 4, u^17, 4, u^3, 4, 1]` (in D) **halts** after 248
epochs, at a step count of 780 bits. The real run is at `[6, 4, u^368, 4, u^17, 4, u^3, 4, 1]` at step 181,429. The
two lists differ only in the counter, so an invariant that excludes the halt has to tell 368 from m0, i.e. follow
`m` mod 2^248 or finer. (From the stack of step 1.1·10^8, `9 u^25 4 u^4 4 u^3 4 1`, odd epochs alone do not empty
it within 10^6 epochs: the price of a halt grows with the stack.)

### No invariant on run parities (Lean)

`lean/NoParityInvariant.lean` proves that **no invariant that sees only the parities of the runs can exclude the
halt**, and the same for the runs mod 4, 8 and 16:

    theorem no_residue_invariant (M : Nat) (hM : M = 2 ∨ M = 4 ∨ M = 8 ∨ M = 16) (S : List Nat → Prop)
        (h0 : S (resW M l0))
        (hc : ∀ l l', D l → S (resW M l) → visit l = some l' → S (resW M l')) :
        ∃ l, D l ∧ S (resW M l) ∧ visit l = none

where `resW M l` is the list of `r % M` over the runs (so it also fixes the number of runs). The proof is an explicit
chain of lists of D for each modulus (14, 18, 20 and 56 lists, found by `py/residue_chain.py`, checked by `decide`
in the kernel; axioms propext and Quot.sound): the first has the residue word of `l0`, `visit` maps each to a list
with the residue word of the next, and the last halts. A search for mod 32 within the same bounds found no chain,
which says nothing either way.

### The counter, 2-adically: 10,000,000 epochs, and how deep the parities dig (22 Nov 2026)

**A fast exact method** (`py/adic.py`). The epoch map is `L' = g(L, p)`, `m' = (3m + c(L, p))/2` with `p = m mod 2`.
Two shortcuts make it cheap: an epoch changes only the top of the stack, so the exact run-stack simulator is run on
the top 8 entries of L (more when the head gets within one entry of the cut, which never happened), with the counter
replaced by 2^64 + 2^33 + p and checked at a second size every 1,000 epochs; and the parity of `m_i` depends only
on `m_0 mod 2^(i+1)`, so the counter is kept exactly but touched in full only once per block of 4,096 epochs
(`2^B m_B = 3^B m_0 + C_B`, `C_(i+1) = 3 C_i + 2^i c_i`), working on the low bits in between. The method agrees
with the exact simulator of `py/visit.py` (parities, stack and counter) over epochs 2,000 to 100,000
(`py/adic.py check 100000`, 47 s).

**10,000,000 epochs, no halt** (`py/adic.py run 1e7`, 8.5 minutes). The counter m then has 5,849,626 bits, the
stack 2,833,499 entries (11,380,629 runs), and the machine has made more than 10^3,521,825 steps (each epoch makes at
least 1.5 m^2 steps). The parities are 49.989% odd, the longest run of odd epochs is 21, of even epochs 25. Entries
of the stack passed by the head in one epoch: 1 in 73.4% of the epochs, 2 in 22.2%, 3 in 4.05%, 4 in 0.26%, 5 in
0.040%, 6 in 2.0e-5, 7 in 3.9e-6, and 8 and 9 once each, the same shares as in the first 100,000 epochs.

**Lean: a parity word is one residue class** (`lean/Adic.lean`, for any stack dynamics `g` and any offsets `c` with
`c ≡ p mod 2`):

    theorem word_class (w : List Bool) (L : S) :
        ∃ r : Int, ∀ m : Int, word g c w.length L m = w ↔ 2 ^ w.length ∣ m - r

The counters that follow a given parity word of length n from a given stack are exactly one class mod 2^n
(`word_eq_iff`: same first n parities iff congruent mod 2^n; `word_onto`: every word occurs). So any event decided by
the parities, such as reaching a depth of the stack or emptying it, happens for a union of residue classes, and its
2-adic (Haar) measure is its probability when fair coin flips replace the parities. A halt from the stack at epoch n
along a parity word w pins the counter at epoch n modulo 2^|w|.

**How deep the parities dig** (`py/dig.py`). Call the *dig* from epoch n the largest drop of the number of runs of
the stack after epoch n. A halt from epoch n needs a dig of the whole stack, |L_n| runs.

| dig ≥ d runs | 1 | 5 | 10 | 15 | 20 | 25 | 30 | 35 |
|---|---|---|---|---|---|---|---|---|
| real run, epochs 2,000 to 1,000,000 (`dig.py real 2e6`) | 0.819 | 0.228 | 0.0357 | 5.0e-3 | 7.9e-4 | 1.1e-4 | 1.6e-5 | 1.0e-6 |
| 2-adic counters: coin flips from the real stack at 6,000 random epochs of [10^5, 3·10^5) (`dig.py along 1e5 3e5 6000 400 1`) | 0.817 | 0.235 | 0.033 | 4.7e-3 | 5.0e-4 | 1.7e-4 (1 of 6,000) | (too rare) | |

The real counter digs exactly as deep as a random 2-adic counter does. The tail is geometric: from d = 10 to d = 30
each further run costs a factor 0.68 (0.56 bits of the counter per run). The deepest dig in the first 10^6 epochs
is 35 runs, while the stack had grown to 10^6 runs. Each epoch changed |L| by -4 to +87 runs (never more than 4
down, in 2·10^6 epochs).

So the precise form of "reaching depth d needs a d-bit pattern" is: the counters that dig d runs from a stack have
2-adic measure about 1.7 · 0.68^d (measured up to d = 30, an estimate, not a bound). A literal bound of d parities
for depth d is false: from the stack of epoch 100,000, some words of 12 parities dig 27 runs
(`dig.py short 100000 15`, every word of length at most 15). Extrapolating the tail to the stack of epoch 10^7
(11,380,629 runs), the 2-adic counters that could still empty it have measure about 10^-1,906,000. A heuristic, like
every probabilistic argument here: the real counter is one integer, and only a proof about its arithmetic (or a
halt found along it) decides the machine.

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
  `no_parity_invariant`, `no_residue_invariant` (`lean/NoParityInvariant.lean`; no invariant on the runs mod 2,
  4, 8 or 16 excludes the halt). `word_class` (`lean/Adic.lean`): the counters that follow a parity word of length
  n are one residue class mod 2^n, for any stack dynamics.
  **native_decide:** `blank_runs_native` (10^7 steps).
- **Trusted computation:** no halt in 100,000 epochs (about 10^35219 steps; 260,000 epochs, about 10^91568 steps, in a
  longer run) with `py/runstack.py`, an exact simulator checked against direct simulation; **no halt in 10,000,000
  epochs** (more than 10^3,521,825 steps) with `py/adic.py`, checked equal to that simulator for 100,000 epochs; the Python visit map
  against the machine at 5,405 visits; a list with the real stack of step 181,429 and the counter m0 halts
  (`py/halting_twin.py`).
- **Exact, by hand from the map:** a halt needs a visit at which all runs but the last two are even. **Trusted
  (enumeration of small lists):** the lists one visit before a halt are `[X, 4, odd, odd, even, ..., even]` (`py/last_step.py`).
- **Heuristic:** the depth the head reaches into the stack falls off geometrically while the stack grows linearly, so
  the probability of ever emptying it is tiny. The real run digs into the stack exactly as often as random 2-adic
  counters do (about 1.7 · 0.68^d for a dig of d runs, `py/dig.py`); extrapolated, the 2-adic counters that could
  still empty the stack of epoch 10^7 have measure about 10^-1,906,000 (a halt from the stack of step 181,429 already needs 247 odd epochs in
  a row on the all-odd route).
- **Open:** whether the orbit of `[12, 1^9]` under the visit map ever reaches a list with only even runs.

## Next steps

An invariant of the visit map that excludes "all runs even" would decide the machine. The parity count of even runs
is not enough, and now provably no invariant on run parities, or on runs mod 4, 8 or 16, can be
(`no_residue_invariant`). A list with the real stack and another counter value halts (`py/halting_twin.py`), so any
proof must follow the counter m modulo 2^248 at least: the exact arithmetic of the 3/2 map `m' = (3m + c)/2`, a
problem of the Mahler 3/2 kind. The real counter digs into the stack like a random 2-adic counter
(`py/dig.py`), so nothing in its parities so far singles it out. Realistic routes are a halt found by following the real orbit further (a halt along
the proved map is a proof), or a structural theorem about which parity words the real m sequence can produce.

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
python3 py/last_step.py        # lists one visit before a halt (about a minute)
python3 py/visit_rules.py | diff - lean/VisitRules.lean
(cd ../../tools/py && python3 -m bbtools.ctl 1RB1RE_1LC1LB_1LE0LD_1LE1LC_0RF1RA_---1RA 4 lean H175628 Blank) | diff - lean/EdgeCert.lean
python3 py/visit.py check 3e7          # the visit map (both forms) against the machine at 5,405 visits, 1 min
python3 py/visit.py epochs 100000      # 100,000 epochs, no halt; depth statistics, 1 min
python3 py/adversary.py bfs 19         # both parities from every stack, a few minutes
python3 py/adversary.py sample 40 2000
python3 py/adic.py check 100000       # the 2-adic method = the exact simulator, epochs 2,000..100,000 (47 s)
python3 py/adic.py run 1e7            # 10,000,000 epochs, no halt (8.5 min)
python3 py/dig.py real 2e6            # how deep the real run digs (100 s)
python3 py/dig.py along 1e5 3e5 6000 400 1   # the same for random 2-adic counters (coin flips, 2.5 min)
python3 py/dig.py short 100000 15     # the deepest dig of every word of at most 15 parities (10 s)
python3 py/halting_twin.py           # a halting list with the stack of step 181,429, under a second
python3 py/residue_chain.py 2 12 300 1   # the mod-2 chain of lean/NoParityInvariant.lean (also 4 12 300 1, 8 12 300 1, 16 18 400 1)
python3 py/epochs.py 1RB1RE_1LC1LB_1LE0LD_1LE1LC_0RF1RA_---1RA 2 1e30 E L "pre:2 4 1^"     # epoch starts, ~1 min
```
