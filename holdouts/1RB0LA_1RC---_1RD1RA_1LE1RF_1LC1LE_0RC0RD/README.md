# 1RB0LA_1RC---_1RD1RA_1LE1RF_1LC1LE_0RC0RD

bbchallenge id 44966. One of the six-state holdouts whose halting from blank tape is open (group G11, family *clock*). It grows to the right like the separator counters of this group.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LA |
| B | 1RC | --- |
| C | 1RD | 1RA |
| D | 1LE | 1RF |
| E | 1LC | 1LE |
| F | 0RC | 0RD |

## What it does

**Events.** At the visits of F to the right end on blank (`tmrun M 3000000000 at F R`) the tape is blocks of 1s
split by single 0s, `1^2 0 1^x ... 0 1^N F>0`, with x in {1, 5, 9, 13} apart from a few blocks at the start of a
phase (2, 6, and after step 2,736,109,137 a fixed block of 41 before N). Within a phase N grows by 4 per event and
the time between events doubles (from step 2,736,109,294: 56, 124, 260, 532, 1076, 2164, 4340, 8692 steps for
N = 10 ... 38). So the last block is a binary counter with 4-cell digits; the left blocks change only next to a
cursor, like the slow counter of `1RB---_1RC0RD_1RD1RA_1LE1RB_0LF0LE_1RF0RD`.

**Rebuilds.** Phases end with a rebuild of the tape: at step 2,114,623 (N 61 to 6) and at step 2,736,109,137
(N 106 to 2). At step 2,878,809,076 N is 90 with 67 blocks on the left.

**Sweep rules** proved in Lean: `a_right_001`, `b_right_001`, `c_right_100`, `d_right_11`, `d_right_100`,
`f_right_11`, `f_right_001`.

**Where it can halt.** `python3 -m bbtools.ctl M 6` closes (not in Lean); it allows a halt only with B reading a 1
with six 1s on its left, inside a long block, as in the separator counters, which halt only when their slow
counter is all ones.

**Larger windows (worker 2, second round).** `python3 -m bbtools.ctl 1RB0LA_1RC---_1RD1RA_1LE1RF_1LC1LE_0RC0RD K` for larger K: K = 7: closes, 1152 abstract configurations where a halt can fire; K = 8: closes, 3456 abstract configurations where a halt can fire; K = 9: no closed set within the default 100 rounds. So larger windows do not remove the halting contexts (their number grows with K) and soon stop closing: this route gave no certificate. These machines are counters, whose halting depends on a global count, which a language of K-cell windows cannot see; a certificate will have to use the macro structure.

**The left string (worker 2, second round, partial).** The left blocks use the pair encoding of the separator
counters: after the first two 1s the cells come in pairs (separator, 1), and a separator 1 is a set bit. The blocks
1, 5, 9, 13 are runs of 0, 2, 4, 6 set bits: set bits come in runs of even length. Read as a binary number (top bit
first), at the events of steps 320, 376, 500, 760 (N = 5, 9, 13, 17) it grows by 3, 12, 48, that is 3·4^(j-1)
with j = (N-1)/4, but carries do not follow plain binary (from step 11,402 to 13,616, N 25 to 29, it grows by
586,752 = 573·2^10). Not decoded further.

**A clock (checked).** On the mirror image `1LB0RA_1LC---_1LD1LA_1RE1LF_1RC1RE_0LC0LD` (left and right swapped), the
batch-3 clock test (`holdouts/1RB0LC_1LC0RB_0LE1LD_1LB1LA_0RA1LF_0LA---/py/clocktest.py 1LB0RA_1LC---_1LD1LA_1RE1LF_1RC1RE_0LC0LD F 2000000 9300 4`) confirms the clock
structure in the phase from step 9,322 (N = 5): the word beyond the block after the visit with block 5 + 4k is
P^(2^k) of the starting word, P one tick from block 5, for k = 1 ... 11 (to step 149,604, N = 49). So the left string
is the state of a word map P iterated 2^k times; the arithmetic above is P's, not plain binary. Proving it for all k
is the clock theorem of `holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE` with growth 4.

**The clock, proved (worker 3, round 2).** `py/counter.py` works on the mirror image (the clock at the left end).
With J j W = `1^(5+4j) 0 W` read from the head, a tick `0^4 D> J j W` -> `D> J (j+1) W'` is

| part | rule | steps |
|---|---|---|
| sweep | `0^4 D> 1^(5+4j) 0` -> `0 1 1 0 0 0 (0000)^j 1 1 1 1 E>` | 4j + 20 |
| excursion (P-step) | `1 E> W` -> `F> 1 W'`, the head stays in the word | depends on W |
| increment | `0000 (1000)^n 1 1 1 F> 1` -> `1000 (0000)^n 1 1 1 1 E>` | 18n + 33 |
| finish | `0 1 1 0 0 0 (1000)^j 1 1 1 F> 1` -> `D> 1^(9+4j) 0` | 14j + 27 |

The block is a binary counter with digits `1000` / `0000` and one excursion per count, so W' = P^(2^j)(W).
`lean/MirrorClock.lean`, theorem `tick`: for every j, if W reaches W' by 2^j P-steps of total cost E (`PChain`),
then `L 0^4 D> J j W` reaches `L D> J (j+1) W'` in exactly E + 51·2^j − 4 steps, for every L. The proof is an
induction on j (`cnt`) over the three rules of `lean/MirrorRules.lean`, each proved for all sizes by
`bbtools.symtm.prove`. It is conditional on the excursions returning. `lean/MirrorBridge.lean` carries it back to
the machine itself (`of_mirror`: every run of the mirror machine, mirrored, is a run of the machine;
`tick_right_end`, `tick`).

**Not vacuous.** `lean/MirrorInstance.lean`: the run of the mirror image from blank tape is at `D> J 0 W` at step
9,321 (`at_start`, by `decide`); the 15 excursions of the next 4 ticks are proved one by one for every tape to the
left (`pstep0` ... `pstep14`), and `run_ticks` takes the run through those ticks with `tick_left_end` (levels 0 to
3: 56, 132, 276, 532 steps) to `D> J 4 W'` at step 10,317.

**Checked against the direct run.** `py/counter.py tmcheck 1e9` (8 minutes): the simulator that does every tick
with returning excursions at once agrees with `tmrun` at all 54 visits of the end in 10^9 steps.

**Next steps.** Everything about halting is now about the word map P: write one excursion as arithmetic on the
left blocks, find what the non-returning excursions (the rebuilds) do, and look for an invariant closed under both
that excludes B on 1. The outside Coq proofs of three other clock machines (busycoq PRs 48, 50, 53) show the kind
of invariant that closes there (a word language with a rational potential).

## Status

- Lean (kernel): `Blank.lean`, `Rules.lean` (seven sweep rules), `MirrorRules.lean` (sweep, increment, finish),
  `MirrorClock.lean` (`tick`, for every j, conditional on the excursions), `MirrorBridge.lean` (back to the machine),
  `MirrorInstance.lean` (the run from blank tape goes through 4 ticks of the theorem).
- Trusted: no halt in 3e9 steps (`tmrun`); CTL with K=6 closed (`bbtools.ctl`); `counter.py tmcheck 1e9`.
- Open: the word map P in the long run, the rebuild rule, halting.

## Scripts

- `py/counter.py`: the clock (`lean` writes `MirrorMachine/MirrorRules/MirrorClock/MirrorBridge.lean`, `instance 9321 4` writes `MirrorInstance.lean`, `tmcheck 1e9` compares with `tmrun`, `run N` follows the phases); uses `clock.py` of `1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE`.
- `py/leanspec.json`: the rules written to `lean/Rules.lean` by `python3 holdouts/1RB---_1RC0RD_1RD1RA_1LE1RB_0LF0LE_1RF0RD/py/leanfiles.py M NS py/leanspec.json lean/`.

## Pages

- [`pages/holdouts/1RB0LA_1RC---_1RD1RA_1LE1RF_1LC1LE_0RC0RD/explainer.html`](../../pages/holdouts/1RB0LA_1RC---_1RD1RA_1LE1RF_1LC1LE_0RC0RD/explainer.html)
- [`pages/holdouts/1RB0LA_1RC---_1RD1RA_1LE1RF_1LC1LE_0RC0RD/proof-status.html`](../../pages/holdouts/1RB0LA_1RC---_1RD1RA_1LE1RF_1LC1LE_0RC0RD/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LA_1RC---_1RD1RA_1LE1RF_1LC1LE_0RC0RD/lean/check.sh
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB1RA_1LC1LE_1RA1LD_0LB0LC_1LF0RE_1LB---`](../1RB1RA_1LC1LE_1RA1LD_0LB0LC_1LF0RE_1LB---/README.md): rename A→E, B→F, C→B, D→C, E→A, F→D and exchange left and right; it is this table started in state E, in a mirror
- [`1RB1RE_1LC1RD_1LA1LC_0RA0RB_1RF0LE_1RA---`](../1RB1RE_1LC1RD_1LA1LC_0RA0RB_1RF0LE_1RA---/README.md): rename A→E, B→F, C→A, D→B, E→C, F→D; it is this table started in state C
- [`1RB---_1RC1RF_1LD1RE_1LB1LD_0RB0RC_1RA0LF`](../1RB---_1RC1RF_1LD1RE_1LB1LD_0RB0RC_1RA0LF/README.md): rename A→F, B→A, C→B, D→C, E→D, F→E; it is this table started in state B

<!-- end of related machines -->
