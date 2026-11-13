# 1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---

bbchallenge id 107543. Group G01. **4/3 counter with a rewritten tail word**: the complete round map is known (exact, depends on m only mod 3), the P-map is proved in Lean for every n, and 100,000 rounds (past 10^24990 steps) do not halt. Open; probviously non-halting, and no halting round is known at all.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LD |
| B | 0RC | 1RD |
| C | 1LA | 1RA |
| D | 1LE | 0LE |
| E | 1RF | 0LA |
| F | 0RA | --- |

## What it does

Sample the run when the head is in state D at the **left** end of the tape. The tape is then

    DL(m, T) = 0^inf D> 1 00 (10)^m T 0^inf          (T a short "tail" word ending in 1)

From blank tape: DL(0, 1) at step 8, DL(3, 1), DL(7, 1), DL(13, 1), …  One **round** DL(m, T) → DL(m′, T′):

1. a right sweep turns every three `10` into two `101` (same length) — `r_ph2a/b/c`;
2. the head rewrites the tail a few cells at a time and turns;
3. the D-loop (`r_dloop`) carries the `(101)` block back to the left end one copy at a time, each copy becoming two
   `01` (the head walks to the left end and back for every copy: a round costs about 3m² steps).

For m ≥ 30 a round depends on m only through r = m mod 3:

    m′ = (4m + c(r, T)) / 3,      T′ = τ(r, T),      steps = a quadratic polynomial in (m − r)/3

| T | r = 0 | r = 1 | r = 2 |
|---|---|---|---|
| `1` | c = 9, T′ = `1` | c = 11, T′ = `1` | c = 1, T′ = `01 0^5 (10)^2 1` |
| `01 0^5 (10)^2 1` | c = 0, `0^3 (10101)^2` | c = −7, `(010)^4 0^4 (10)^2 1` | c = 13, `1^2 (01)^2` |

With T = 1 this is the P-map of the first analysis (P(n) = `(101)^n 01 A>` is the moment just before
DL(2n+1, 1)): P(3k) → P(4k+2), P(3k+1) → P(4k+3), P(3k+2) → `(101)^(4k+4) 110101 A>`, the start of a tail.
`py/roundmap.py` computes each round from four small representatives m0 = 3j + r (j = 10..13), checks that they
agree, and caches it; a round with a 12,000-digit m costs as much as one with m ≈ 30.

The tails are lists of small blocks (`(010)^a`, `(10)^b`, `1^2 (01)^c`, …) separated by runs of zeros. Driven by
m mod 3, which behaves like a three-sided coin, the tail does a recurrent random walk: in the first 100,000 rounds
it is back to `1` 9,214 times and is never longer than 106 cells (18,555 (r, T) pairs used).

**Halting.** The machine halts exactly when D reads a 0 with a 0 on its left (D writes 1 and steps left, E steps
back right onto that 1 as F, F1 halts). This can only happen inside a tail rewrite. No such round is known: a
breadth-first search of the tail graph with every residue allowed (30,000 tails, 90,000 rounds) finds none.

**Heuristic.** m grows by 4/3 per round forever; the tail is a recurrent process on a language in which no halting
round has been found. Probviously non-halting, and halting would need a tail outside everything explored; this
suggests an invariant of the tail language that a proof could use.

## What is proved

| level | result | where |
|---|---|---|
| kernel | halting configurations; no halt in 10⁴ steps (10⁷ by native_decide) | `lean/Blank.lean` |
| kernel | the P-map for every n, with step counts 27k²+87k+35, 27k²+105k+62, 27k²+123k+117 | `p0`, `p1`, `p2`, `lean/Macro.lean` |
| kernel | the D-loop iterated, with any tape to its right: `(101)^a D> 10 (01)^b R` → `D> 10 (01)^(b+2a) R` in 3a²+17a steps | `diter`, `lean/Macro.lean` |
| kernel | blank tape → P(1) (14 steps) → … → P(59) → `(101)^80 110101 A>` (27,264 steps) | `blank_Q80` |
| trusted | no halt in 10⁹ steps | `holdouts/triage.json` |
| trusted | the round map = every DL event of the direct run up to 5·10⁹ steps (31 events) | `py/roundmap.py check 5e9` |
| trusted | a round depends on m only mod 3 (four representatives per (r, T) used) | `py/roundmap.py` |
| trusted | 100,000 rounds without a halt (last one past 10^24990 steps, m ≈ 10^12494) | `py/roundmap.py iterate 100000` (1 min) |
| heuristic | no halting round among 90,000 explored | `py/roundmap.py bfs 30000 90` (25 min) |
| open | halting | |

## Reproduce

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---/lean/check.sh
cd holdouts/1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---/py
python3 rules.py > ../lean/Rules.lean      # regenerate the rules
python3 roundmap.py check 5e9              # 20 s
python3 roundmap.py iterate 100000         # 1 min
python3 roundmap.py show 40                # the DL events with their tails
```

## Further work

- Prove each round in Lean with symbolic k (state the sweep through a given tail with `bbtools.symtm.prove` and
  compose with `diter`, which already allows any tail); then an orbit theorem as in
  `1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE/lean/Orbit.lean`, with a table of the tails used.
- Describe the tail language by a grammar and τ as a transducer; look for an invariant excluding the halting
  pattern (that would decide the machine).
- `py/explore.py`, `py/sim.py` are the first pass's tools (P-map check, synthetic starts).

## Remainder classes (family survey)

- **Rounds between end events, by remainder class** (trusted). Sample the run whenever the head is in state D reading 1 with only 0s to its left. Read rightwards from the head, the tape is then `A U^m B`: one long periodic block between two short context words. For each class (A, U, B, m mod 3) the next sample is simulated for six values of m and extended as an affine map of m (with a cubic step count). Along the direct run from blank tape to 3·10^9 steps (30 events) the class map predicts the next event in all 21 rounds it applies to. This is an extrapolation checked by computation, not a proof. Command: `python3 holdouts/1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---/py/ctxround.py 1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA--- L D 1 check 3e9`
- **309,710 rounds of the class map without a halt** (heuristic). Iterated with exact integers from the event at step 14,535 of the run (A = `10`, U = `01`, m = 88, B = `(empty)`): 309,710 rounds without meeting a halting class; m then has 128,548 bits (about 10^77,393 steps of the machine). 29,114 distinct contexts occur, the longest of 120 cells. Command: `python3 holdouts/1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---/py/ctxround.py 1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA--- L D 1 orbit 309710`
- **No halting class among 5,000 contexts** (heuristic). Breadth first from the starting context, with every remainder at every context (whether or not the numbers can really produce that sequence of remainders, and only for m large compared with the contexts): 5,000 contexts expanded, 9,484 found, to depth 13. None of them halts; the search is not complete (the set of contexts keeps growing), and it says nothing about a halt that needs a context as long as the block itself. Command: `python3 holdouts/1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---/py/ctxround.py 1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA--- L D 1 bfs 5000`

## Pages

- [`pages/holdouts/1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---/explainer.html`](../../pages/holdouts/1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---/explainer.html)
- [`pages/holdouts/1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---/proof-status.html`](../../pages/holdouts/1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---/proof-status.html)
