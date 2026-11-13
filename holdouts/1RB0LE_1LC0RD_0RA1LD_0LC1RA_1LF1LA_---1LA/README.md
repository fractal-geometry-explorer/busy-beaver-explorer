# 1RB0LE_1LC0RD_0RA1LD_0LC1RA_1LF1LA_---1LA

bbchallenge id 30875. Group G01. **4/3 counter with a tail list of runs** (same family as 1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---): the complete round map is known and exact; 100,000 rounds (past 10^24990 steps) do not halt. Open; probviously non-halting, no halting round known.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LE |
| B | 1LC | 0RD |
| C | 0RA | 1LD |
| D | 0LC | 1RA |
| E | 1LF | 1LA |
| F | --- | 1LA |

## What it does

Sample the run when the head is in state E at the **left** end reading 1. The tape is then

    EL(m, T) = 0^inf E> 1 00 1^m T 0^inf          T = 0 1^(a1) 0 1^(a2) … (a list of runs; [] = empty)

From blank tape: EL(11, [2]) at step 213, EL(21, [2]), EL(25, [7, 2]), EL(43, [2]), EL(62, []), …  One round
sweeps the run, rewrites it as about 4m/3 ones, rewrites the list, and comes back. Once m is large compared with
the list, a round depends on m only through r = m mod 3:

    m′ = (4m + c(r, T)) / 3,      T′ = τ(r, T),      steps = a quadratic polynomial in (m − r)/3

| T | r = 0 | r = 1 | r = 2 |
|---|---|---|---|
| [] | [2] | [] | [2] |
| [2] | [7, 2] | [] | [2] |
| [7, 2] | [2] | [2] | [17, 2] |
| [17, 2] | [17, 7, 2] | [2] | [7, 2] |
| [39, 2] | [54] | [2] | [] |

The first run a of the list is a second counter: while r ≠ 1 it grows by about 4/3 (with a short `2` or `7, 2`
behind it), and for r = 1 it is swallowed by m (m′ = (4m + 3a + 8)/3, T′ = the rest). In 100,000 rounds from blank
tape only 44 (r, T) pairs occur, the list is back to [2] in 47,685 rounds, and it is never longer than 249 cells.

The earlier "D-events `0 (101)^n W D>`" of the first analysis are moments inside these rounds.

**Halting.** A halt (F reading 1) can only happen while a list is rewritten. No such round is known: all rounds of
the run, every list reachable within 400 cells with any residues (20 lists), and 4,485 synthetic rounds (first run
a < 300 followed by [], [2], [7, 2], [17, 2] or [17, 7, 2], all residues) return to the EL form.

**Heuristic.** m grows by 4/3 per round forever and the list resets every few rounds; probviously non-halting, and no
way to halt is known.

## What is proved

| level | result | where |
|---|---|---|
| kernel | halting configurations; no halt in 10⁴ steps (10⁷ by native_decide) | `lean/Blank.lean` |
| trusted | no halt in 10⁹ steps | `holdouts/triage.json` |
| trusted | the round map = every EL event of the direct run up to 5·10⁹ steps (30 events) | `py/roundmap.py check 5e9` |
| trusted | a round depends on m only mod 3 (five representatives, m large compared with T) | `py/roundmap.py` |
| trusted | 100,000 rounds without a halt (last past 10^24990 steps) | `py/roundmap.py iterate 100000` (25 s) |
| heuristic | no halting round among all lists reachable within 400 cells and 4,485 synthetic rounds | `py/roundmap.py bfs 3000 400` |
| open | halting | |

## Reproduce

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LE_1LC0RD_0RA1LD_0LC1RA_1LF1LA_---1LA/lean/check.sh
cd holdouts/1RB0LE_1LC0RD_0RA1LD_0LC1RA_1LF1LA_---1LA/py
python3 roundmap.py check 5e9      # 20 s
python3 roundmap.py iterate 100000 # 25 s
python3 roundmap.py show 40        # the events with their lists
```

The engine (`RoundMap`, its C helper `c/evrun.c`) lives in `../1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---/py/rounds.py`.

## Further work

- Write τ and c in closed form for lists [a] + suffix (a in residue classes mod 3 or 9) and prove that no round halts;
  that would decide the machine. Then Lean: the round rules with symbolic m (as for the cousin machine's `diter`).

## Third pass: the halting condition, and why no regular invariant exists

**The first run of the list drains the main run.** With T = [a, …] (`py/drain.py`, direct simulation):

- r = m mod 3 = 1: a is swallowed, m′ = (4m + 3a + 8)/3, and the list loses its first run. No halt, for any a.
- r = 0 or 2: for a in three residues of twelve a is swallowed as well; otherwise a survives with a′ = 4a/3 + O(1)
  and **m′ = (4m − a)/3 + O(1)**: the main run pays for the growth of a. With x = a/m this is 1/x′ = 1/x − 1/4.
- **EL(m, [a, …]) halts** (before the next EL event) when m ≢ 1 (mod 3) and a ≥ 4m + 14 (m ≡ 0) or a ≥ 4m
  (m ≡ 2), up to 12 less when more runs follow; beyond the threshold all a but about 5% (some just above it) halt.
  Checked for every m < 30, a < 200 and the suffixes [], [2], [7, 2] (`py/drain.py halt 30 200`).

So the machine halts exactly if a first run survives long enough to reach four times the main run. A first run is
born small (2, 7, 17, … in the run) and survives a round with probability about 1/2 (r ≠ 1, and a outside the
three swallowed residues); to reach 4m it must survive about 4m/a₀ rounds in a row. At round 40 of the run m is
2.3·10⁶ and grows by 4/3 per round, so the chance of that streak is below 2^(−100,000) and falls doubly
exponentially: **probviously non-halting**. In 100,000 rounds the longest list is 249 cells.

**No closed regular language can prove it.** The first run is unbounded along the run (heuristically: streaks of
every length occur). A regular set containing `E> 1 00 1^m 0 1^a …` for unboundedly many a contains, by pumping,
`1^m 0 1^(a + kp)` for all k with m fixed, hence configurations with a ≥ 4m + 14 in every residue class, and those
halt. So any regular invariant of the whole run that excludes a halt would have to prove that the first run stays
bounded, which is false if the residues m mod 3 behave randomly. This is why the search for a tail language fails,
and it is checked by experiment: `py/pdsx.py` (the pushdown reduction with any DFA, with an export to `TM.CTL`)
reaches a halt with every DFA tried — all DFAs with at most 6 states on either side (`bb6-1RB0LF_1RC0LB/c/pds.c`),
windows of up to 4 cells with counters modulo 3, and DFAs learned from the left words of the run (up to 16,638
states). The community tracker calls the machine a "lottery" ("a 4/3 Bell where a second counter drains the main
one"), which is this mechanism. A proof would need a number-theoretic bound on the streaks of m mod 3 ≠ 1 under
m → (4m + c)/3, a Collatz-like statement.

The sibling 1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA--- is not touched here (a busycoq PR was open on it).

The macro simulator `c/msim.c` (a copy of the one in holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---, in
`../1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA/c/`; blocks of 6 cells; checked against the direct simulator at 10⁹ steps by `check_msim.py check`) runs
10¹⁸ steps from blank tape without a halt: `python3 ../1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA/py/check_msim.py run 1RB0LE_1LC0RD_0RA1LD_0LC1RA_1LF1LA_---1LA 1e18` (2 to 5 minutes).

## Remainder classes (family survey)

- **Rounds between end events, by remainder class** (trusted). Sample the run whenever the head is in state D reading 1 with only 0s to its left. Read rightwards from the head, the tape is then `A U^m B`: one long periodic block between two short context words. For each class (A, U, B, m mod 3) the next sample is simulated for six values of m and extended as an affine map of m (with a cubic step count). Along the direct run from blank tape to 3·10^9 steps (31 events) the class map predicts the next event in all 22 rounds it applies to. This is an extrapolation checked by computation, not a proof. Command: `python3 holdouts/1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---/py/ctxround.py 1RB0LE_1LC0RD_0RA1LD_0LC1RA_1LF1LA_---1LA L D 1 check 3e9`
- **376,892 rounds of the class map without a halt** (heuristic). Iterated with exact integers from the event at step 7,961 of the run (A = `110`, U = `1`, m = 117, B = `011`): 376,892 rounds without meeting a halting class; m then has 156,432 bits (about 10^94,180 steps of the machine). 23 distinct contexts occur, the longest of 790 cells. Command: `python3 holdouts/1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---/py/ctxround.py 1RB0LE_1LC0RD_0RA1LD_0LC1RA_1LF1LA_---1LA L D 1 orbit 376892`

## Pages

- [`pages/holdouts/1RB0LE_1LC0RD_0RA1LD_0LC1RA_1LF1LA_---1LA/explainer.html`](../../pages/holdouts/1RB0LE_1LC0RD_0RA1LD_0LC1RA_1LF1LA_---1LA/explainer.html)
- [`pages/holdouts/1RB0LE_1LC0RD_0RA1LD_0LC1RA_1LF1LA_---1LA/proof-status.html`](../../pages/holdouts/1RB0LE_1LC0RD_0RA1LD_0LC1RA_1LF1LA_---1LA/proof-status.html)
