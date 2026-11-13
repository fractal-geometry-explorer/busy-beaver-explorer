# 1RB0LF_1LC0RB_0LD1LA_0RA1LE_0LA0RA_1LA---

bbchallenge id 9146. One of the six-state holdouts whose halting from blank tape is open.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LF |
| B | 1LC | 0RB |
| C | 0LD | 1LA |
| D | 0RA | 1LE |
| E | 0LA | 0RA |
| F | 1LA | --- |

## What it does

**Tape**: words `10` and `110`. **Sample point**: a round starts with A on the leftmost cell and

    A> (10)^4 110 (10)^N 100 T        T = (10)^12 1  (short)   or   10 (10)^m 110 (10)^9 1001 1  (long)

**Counting phase (proved)**: the tape is `(10)^a 110 (10)^b 10010 (110)^c ...` and one sweep gives
(a, b, c) -> (a+3, b-2, c+1) in 14a + 8b + 83 steps (`sweep` in `lean/Rules.lean`, for all a, b, c and any tape
beyond). The sweeps never cross the (110)^c part; the left end grows by 5 cells a sweep (the square-root side).

**Conversion (proved)**: when b reaches 0 or 1, the (110)^c part is turned back into pairs and the next round
starts (`lean/Conv.lean`, eight symbolic runs from `py/round.py`). With RS(N, T) the round start above, Lean proves
four whole-round branches (`lean/Round.lean`), each for every j and m, with an exact step count:

    round_A: RS(4j+5, Ts)      -> RS(6j+10, Tl(3j+6))         N = 1 mod 4:  N -> (3N+5)/2, long tail
    round_B: RS(4j+2, Tl m)    -> RS(9j+m+27, Ts)             N = 2 mod 4, long tail
    round_C: RS(4j+4, Ts)      -> RS(9j+33, Ts)               N = 0 mod 4:  N -> 9N/4 + 24
    round_D: RS(4j+4, Tl m)    -> RS(6j+11, TD(3j+m+5))       N = 0 mod 4, long tail -> new tail TD

with Ts = (10)^11 1, Tl m = (10)^m 1 (10)^11 0101, TD p = 1 (10)^p 1 (10)^9 0101101 (written from the 10010 on).
Rounds from blank tape: N = 13, 22, 84, 213, 322, 909, 1366, 3780, 8529, 12796, 19199 (branches A B C A B A B C A D);
`reach_19199` proves the machine is at RS(19199, TD 15998) at exactly step 1,842,640,229.

The round from N = 19199 (3 mod 4, tail TD) ends in a left-end shape not covered by the branches; a macro simulation
finds the next left-end start at step 4,516,954,072: `A> (10)^4 110 (10)^28802 1 110 (10)^30401 110 (10)^5 10010 (110)^2 1`,
where the run is followed by `1 110` instead of `10010`.
A Collatz-like map whose branch depends on N mod 4 and the tail shape; the tail grows slowly and changes shape.

**Halting**: F on a 1 halts and F is entered only from A on a 1, so it halts iff `1 A> 1` occurs. In 10^9 steps A read
a 1 92,274,763 times, always with a 0 to its left.

## Status

Open.

- **Lean, kernel** (`lean/Rules.lean`, from `py/rules.py`): `sweep` (the counting phase), `b_run`, `f_run`, `a_run`,
  `halt_shape`, `halt_after_shape`. `lean/Blank.lean`: no halt in 10^7 steps. `lean/Conv.lean` (from `py/round.py`):
  `sweep0`, `first`, the eight conversions `convA` ... `convH`. `lean/Round.lean`: `sweeps` (k sweeps at once),
  `round_A`, `round_B`, `round_C`, `round_D`, `reach_19199`, `no_halt_1842640229` (no halt in the first
  1,842,640,229 steps).
- **Trusted**: no halt in 10^9 steps; the near-miss count (`c/nbhd.c`); the round start at step 4,516,954,072.
- **Open**: the round map is not closed: new tail shapes keep appearing (TD at 19199, another at 28802).

## Notes for later

- `py/orbit.py` runs the symbolic orbit from RS(19199, TD 15998) and stops at the first unproved shape; extend the
  conversions to the TD tail and to the tail at N = 28802, then look for a tail family that is closed under rounds.
- If the tails do form a finite family of parametric shapes, the round map is a theorem and the question reduces to
  its orbit, as for the other G02 machines.

## Reproduce

```sh
gcc -O2 -o tok holdouts/1RB0LF_1LC0RB_0LD1LA_0RA1LE_0LA0RA_1LA---/c/tok.c && ./tok 1RB0LF_1LC0RB_0LD1LA_0RA1LE_0LA0RA_1LA--- 2000000000 A 1 L 0 100000 1 | grep '| 1x4 2 1x'   # round starts
gcc -O2 -o nbhd holdouts/1RB0LF_1LC0RB_0LD1LA_0RA1LE_0LA0RA_1LA---/c/nbhd.c && ./nbhd 1RB0LF_1LC0RB_0LD1LA_0RA1LE_0LA0RA_1LA--- 1000000000 A 1
python3 holdouts/1RB0LF_1LC0RB_0LD1LA_0RA1LE_0LA0RA_1LA---/py/rules.py > holdouts/1RB0LF_1LC0RB_0LD1LA_0RA1LE_0LA0RA_1LA---/lean/Rules.lean
```

## Pages

- [`pages/holdouts/1RB0LF_1LC0RB_0LD1LA_0RA1LE_0LA0RA_1LA---/explainer.html`](../../pages/holdouts/1RB0LF_1LC0RB_0LD1LA_0RA1LE_0LA0RA_1LA---/explainer.html)
- [`pages/holdouts/1RB0LF_1LC0RB_0LD1LA_0RA1LE_0LA0RA_1LA---/proof-status.html`](../../pages/holdouts/1RB0LF_1LC0RB_0LD1LA_0RA1LE_0LA0RA_1LA---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LF_1LC0RB_0LD1LA_0RA1LE_0LA0RA_1LA---/lean/check.sh
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0LA_0RC1RD_0LD1RE_1LA0RF_0RD0LD_1RD---`](../1RB0LA_0RC1RD_0LD1RE_1LA0RF_0RD0LD_1RD---/README.md): rename A→D, B→A, C→B, D→C, E→E, F→F and exchange left and right; it is this table started in state B, in a mirror

<!-- end of related machines -->
