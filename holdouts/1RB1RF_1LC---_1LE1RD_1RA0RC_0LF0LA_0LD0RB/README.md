# 1RB1RF_1LC---_1LE1RD_1RA0RC_0LF0LA_0LD0RB

bbchallenge id 132148. One of the six-state holdouts whose halting from blank tape is open.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RF |
| B | 1LC | --- |
| C | 1LE | 1RD |
| D | 1RA | 0RC |
| E | 0LF | 0LA |
| F | 0LD | 0RB |

## What it does: a two-counter map at the left end

Each time the head turns at the left end, in state A two cells left of the tape or in state D three cells left of
it, the tape is

    1^n (01)^k 111        or, with k = 0,       1^n        (everything else blank)

Write these left-end states A(n, k) and D(n, k). From blank tape the first one is D(3, 0), after 11 steps. The
next left-end state is given by this map (`py/emap.py`; "other" means the other letter):

| state | condition | next |
|---|---|---|
| A(n, 0), D(n, 0) | n even | other(n + 3, 0) |
| A(n, 0) | n odd | D(1, (n+1)/2) |
| D(n, 0) | n odd | D(3, (n+1)/2) |
| s(n, k), n even | k >= 2 | other(n + 4, k - 1) &nbsp; (*drain*) |
| | k = 1 | other(n + 7, 0) |
| s(n, k), n odd | 2k > n + 5 | D(2n + 7, k - (n+5)/2) resp. A(2n + 6, k - (n+5)/2) &nbsp; (*doubling*) |
| | 2k = n + 5 | D(2n + 10, 0) resp. A(2n + 9, 0) |
| | 2 <= k, 2k < n + 5 | other(n - 2k + 6, 2k) &nbsp; (*failed doubling*) |
| | k = 1 | **halt** |

In words: an all-ones tape of odd length is turned into a short block of ones and a long block of `01`s
(*conversion*). While n is odd the machine tries to *double* the ones, paying (n+5)/2 pairs `01` for it; when it
cannot pay, it gives the ones back and doubles the `01` block instead, changing side, until it can pay. A doubling
in A leaves n even, and then the *drain* turns each `01` into four 1s until the tape is all ones again. D(N, 0) is
what the earlier notes called the start of an epoch (`1 A>0 0 1^N` one step later): from blank tape

    N = 3, 124, 583, 2143, 8167, 34679, 125063, 329599, 958615, 1213191, 2231495, 8601719, ...

For example D(3,0) -> D(3,2) -> A(5,4) -> D(3,8) -> D(13,4) -> A(11,8) -> A(31,0) -> D(1,16) -> D(9,13) -> D(25,6)
-> A(19,12) -> A(47,0) -> D(1,24) -> ... -> D(124,0). N grows by a factor 2.3 per epoch on average, the step count
goes like N^2, and the tape grows to the left like the square root of the step count; the right end only moves by a
few cells.

The map is **computed and checked, not proved**: `py/leftcheck.py` runs the plain machine from built tapes and
compares: all 7,000 states with n < 70 and k < 50, 300 random states with n up to 400 and k up to 300, the first 170
left-end states of the blank-tape run, and every epoch N = 1..150 to its end. The epoch values the map gives also
agree with all 126 epochs of the independent accelerated run to 10^100 steps (`py/run.py`).

## Does it halt?

The only halt is B reading 1. In terms of the map it happens exactly from a state with n odd and k = 1, and such a
state arises only from a doubling in D that leaves exactly one pair (a doubling in A makes n even, a failed doubling
makes k even):

**the machine halts iff the orbit of the map from D(3, 0) reaches a state D(n, k) with n odd and 2k = n + 7.**

(Then D(n, k) -> D(2n + 7, 1) -> halt, within the next sweeps; `halt_even` in `lean/Rules.lean` is the kind of
sweep that stops the machine: state D over an even block of ones before `0 111`.) This also explains the halting epochs: N = 1, 4, 6, 9, 18, 26, 27, 48, 65, 106,
110, 123, 128, 143, ... are the N whose orbit from D(N, 0) meets 2k = n + 7 in D before the next epoch; e.g. N = 26:
D(26,0) -> A(29,0) -> D(1,15) -> D(9,12) -> D(25,5) -> A(21,10) -> D(7,20) -> D(21,14) -> D(49,1) -> halt.

From blank tape the map has been iterated for **8,598 epochs without a halt** (`py/orbit.py 280`, 9.1·10^7 map
steps, a run of drain steps counted as one): the last epoch value N has 10,317 bits, so the machine has run more than
10^3,100 steps (an epoch takes more than N steps; about N^2, so really about 10^6,200). The accelerated run of the
machine itself covers the first 414 epochs (10^300 steps).

**Heuristic.** Each doubling stage in D ends with a remainder k - (n+5)/2 that is some number between 0 and about
n/2, and a halt needs it to be exactly 1. If the remainders behave like random numbers the chance is about 2/n per
stage, and n grows geometrically along the orbit, so the expected number of future halts is a geometric series
dominated by the current term: around 2^-10,000 now. The machine almost certainly does not halt; a proof would have
to control exact remainders of an exponentially growing orbit of a Collatz-like map.

## For later

Stopped at: the complete left-end map on (state, n, k) and the halting condition in terms of it, checked against
the plain machine but not proved; in Lean only the drain and the halting sweep. Next: prove the map in Lean and the
reduction `HaltsFromBlank <-> the orbit reaches D(n, (n+7)/2), n odd` (as in
`holdouts/1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD/lean/Reduction.lean`). The drain rows are `drain` in
`lean/Rules.lean` (two trips at a time) plus the end k = 1. The conversion rows are a loop of sweeps
(`bbtools.cycles`). The doubling rows are the hard part: a nested zig-zag in the middle of the tape, an outer loop
(one pair `01` paid per step) over an inner linear cycle; it needs an induction on the number of pairs paid, with
the invariant tape found from `py/leftcheck.py`-style traces (print the tape at every turn inside one doubling).
The failed doubling is the same loop running out of pairs.

## Files

- `py/emap.py`: the left-end map (`step`, and `jump`, which does a run of drain steps at once).
- `py/leftcheck.py`: the map against the plain machine (grid of states, random states, the blank-tape run, epochs).
- `py/orbit.py`: iterates the map from blank tape for a given number of seconds; `orbit.py epochs K` prints the
  first K epoch values.
- `lean/Rules.lean` (generated by `py/rules.py`): `drain`, `halt_even` with `halt_even_stop`, `pass_odd`.
- `py/turnacc.py`: the accelerator of the machine itself. It samples at every *turn* of the head, re-tokenises the
  tape with the words `1`, `01`, `10`, and when samples with the same shape have counts in arithmetic progression
  and step counts whose increments are a polynomial in the cycle index (degree up to 4), applies the cycle many
  times at once. It is an extrapolation; `python3 py/run.py check 3e8` compares every accelerated sample with the
  plain run-length simulator `py/rlsim.py` (8,828 samples, all equal).
- `py/run.py`: the run from blank tape with that accelerator, printing every epoch start (steps, N).
- `py/epoch.py`: the epoch map f(N) from a built tape with the accelerator, `scan` for the halting N.

## Status

Open. Lean (`lean/Blank.lean`): the halting configurations (`step_none_iff`), no halt in 10,000 steps by
the kernel, in 10,000,000 by `native_decide`. Lean (`lean/Rules.lean`, kernel): the drain, how a halt happens.
C (`tools/c/triage.c`): no halt in 1,000,000,000 steps. Python: no halt in 10^300 steps of the machine
(`py/run.py`, extrapolated cycles, checked against plain simulation up to 3·10^8), and in 8,598 epochs of the
left-end map (`py/orbit.py`, more than 10^3,100 steps), the map being checked against the plain machine but not
proved.

## Pages

- [`pages/holdouts/1RB1RF_1LC---_1LE1RD_1RA0RC_0LF0LA_0LD0RB/explainer.html`](../../pages/holdouts/1RB1RF_1LC---_1LE1RD_1RA0RC_0LF0LA_0LD0RB/explainer.html)
- [`pages/holdouts/1RB1RF_1LC---_1LE1RD_1RA0RC_0LF0LA_0LD0RB/proof-status.html`](../../pages/holdouts/1RB1RF_1LC---_1LE1RD_1RA0RC_0LF0LA_0LD0RB/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RF_1LC---_1LE1RD_1RA0RC_0LF0LA_0LD0RB/lean/check.sh
python3 holdouts/1RB1RF_1LC---_1LE1RD_1RA0RC_0LF0LA_0LD0RB/py/run.py check 3e8
python3 holdouts/1RB1RF_1LC---_1LE1RD_1RA0RC_0LF0LA_0LD0RB/py/run.py 1e100
python3 holdouts/1RB1RF_1LC---_1LE1RD_1RA0RC_0LF0LA_0LD0RB/py/epoch.py scan 1 3000
python3 holdouts/1RB1RF_1LC---_1LE1RD_1RA0RC_0LF0LA_0LD0RB/py/leftcheck.py
python3 holdouts/1RB1RF_1LC---_1LE1RD_1RA0RC_0LF0LA_0LD0RB/py/orbit.py 60
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB---_1RC1LE_0RD0RF_0RE0LA_1LF0LB_1LA1LD`](../1RB---_1RC1LE_0RD0RF_0RE0LA_1LF0LB_1LA1LD/README.md): rename A→F, B→A, C→B, D→E, E→C, F→D and exchange left and right; it is this table started in state B, in a mirror

<!-- end of related machines -->
