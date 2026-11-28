# Which halt hunts are worth their compute (26 November 2026)

Section E of [`technique-survey-nov26.md`](technique-survey-nov26.md) asked for two things: the segmented Coq
replay of 1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC as a tool for other machines, and an estimate, for each proved
map, of how many halts a run should expect, so that hunts can be ranked. The tool is
[`tools/segreplay`](../../tools/segreplay/README.md). This note is the ranking. Nothing here decides a machine. The
estimates are heuristic and were computed, not proved.

## The estimate

The probe follows the orbit of a machine's visit map. At sample visits it makes 256 copies of the state, moves
every count by a small random amount, and follows each copy for 4,000 visits. From the fraction of copies that
halt it gets a halting rate per visit for "states like the orbit's", and from that the number of halts the orbit
itself should expect while its visit index doubles. If that number stays the same from doubling to doubling, the
expected count grows like the logarithm of the run length: a halt is expected eventually, and every doubling buys
the same chance. Each machine was probed three times: counts moved by any amount up to 8, by even amounts, and by
multiples of 6. The last two keep parities and residues mod 3, so a drop between them shows a residue that
protects the orbit.

**Calibration.** 1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC is the one machine of this kind whose answer is known:
it halts at visit 79,859,656,218,974, in the 47th doubling. The probe gives 0.034 expected hits per doubling,
the same in all three settings and steady from doubling 13 to 22. That is about 1.2 expected hits by the time it
halted. So the probe is at least of the right size there.

**A second check, and what it showed instead: orbits merge.** The direct test of the estimate is to follow
perturbed copies for many doublings and count how many halt (`run ens`). For 1,000 copies started between visits
2^14 and 2^18 and followed to visit 2^24:

| machine | halted | the estimate predicts | the 1,000 copies at the end |
|---|---|---|---|
| 1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC | 229 | about 230 | 771 running, on 15 different orbits, 107 of them on the blank-tape orbit itself |
| 1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD | 311 | about 290 | 688 running, on 163 orbits, 8 on the blank-tape orbit |
| 1RB1RF_0LC0RF_1RD1LC_---0LE_0RC1LF_1RA0LE | 49 | about 340 | 949 running, on 68 orbits, 188 on the blank-tape orbit |

The totals agree for the first two, but the copies are not independent samples. Different starts run into the
same orbit, shifted in time, and the merging goes on: a longer run of 400 copies of the third machine left 362
running on only 3 orbits. The halts come in bursts for the same reason (163 of the 229 in one doubling: one
merged orbit halting). So this test cannot confirm the estimate, and it changes what the estimate means. The
probe measures how often a *freshly moved* state halts before it merges. Whether the few orbits that everything
merges into halt at the same rate is a separate question, and for the third machine the answer in this window is
no: not one copy halted after visit 2^19.

(27 November: [`followup/contrast-merge.md`](followup/contrast-merge.md) follows this up with every state below a
level instead of 1,000 copies. The 49 is the figure for all tapes of those levels, 5.1%, and the merging is a
property of the map, which is two-to-one on levels that grow slowly. Over 16 octaves all tapes together halt at
8.6% per octave, as estimated.)

## Results

| machine | expected hits per doubling of visits | residues matter? | run so far | expected so far | observed |
|---|---|---|---|---|---|
| 1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC (calibration) | 0.034 | no | to the halt, 2^46 visits | 1.2 | **halt** |
| 1RB1RF_0LC0RF_1RD1LC_---0LE_0RC1LF_1RA0LE | 0.056 | no (0.056, 0.056, 0.060) | 5.07·10^12 rules, about 2^83 frames (2.9·10^21 frames at 10^11 rules, growing like the square) | about 3.9 | no halt |
| 1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD | 0.045 | no (0.045, 0.058, 0.060) | 1.4·10^25 frames (2^83.5; 6·10^12 passes of `c/crun`, run on 27 November from the 1.3·10^23 frames this note first used) | about 3.2 | no halt |
| 1RB1RD_0LC1RA_1RA1LC_0RB1LE_1RF0LD_---0RE | 0.0007 | halves (0.0003) | 10^11 phases (2^36.5) | about 0.02 | no halt |
| 1RB1RD_0LC1RA_0RA1LC_1RA1LE_1RF0LD_---0RE | 0.0006 | yes: too few halts to measure with even moves | 10^11 phases | about 0.02 | no halt |
| 1RB1RF_1LC1LF_0RE1LD_0LB1LD_---1RC_1RA0RD | 0.0005 | yes: too few with even moves; 6% of copies leave the described tapes | 10^11 phases | about 0.01 | no halt |
| 1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE | 0.0002 | yes: too few with even moves | 10^11 phases | below 0.01 | no halt |
| 1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_---0RE | about 0.0003 at doublings 10 to 13, too few halts later | yes | 10^11 phases | below 0.01 | no halt |

"Visits" are applications of the map each row was probed with: frames of `Phases.lean` for the second and third
machines, phases of `Phases.lean` for the last five. "Expected so far" is the rate times the number of doublings
since doubling 12. The raw probe output is in `tools/segreplay/probes/`, and
`python3 tools/segreplay/segreplay.py hits SPEC PROBE 4000` prints each table.

For 1RB1RF_0LC0RF_1RD1LC_---0LE_0RC1LF_1RA0LE the machine's own folder had counted near misses of the halting tape
directly and found 3.4 expected hits by 5.07·10^12 rules, growing by 0.26 per tenfold growth of x. The probe is a
different method and gives 3.9 and about 0.37 (a tenfold growth of x is 6.6 doublings of frames). The two agree to
within the spread of either.

## Reading

1. **Two machines are in the same regime as the machine that halted.** 1RB1RF_0LC0RF_1RD1LC_---0LE_0RC1LF_1RA0LE
   and 1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD each expect about 0.05 hits per doubling, steadily, with no residue
   protecting them. Each has already run through about 3 expected hits without halting. Taken alone that happens
   2 to 6 times in a hundred; for both at once, about once in a thousand. Either the estimate is high by a factor
   of two or three for these two (it was not for the calibration machine), or the orbits avoid the halting set
   for a reason that is not a parity or a residue mod 3. The merging above is a candidate for that reason: the
   blank-tape orbit is one of a few orbits that nearly every start joins, and such an orbit need not look like a
   typical neighbour. This is the most useful thing the table says: **these
   two deserve a search for an invariant as much as a longer run.** One caution against reading too much into
   the product: these two are on the list *because* they have not halted. Machines of the same kind that did
   halt early (the calibration machine is one) are no longer holdouts, so a few survivors with 3 expected hits
   behind them are what the same estimate predicts for the list as a whole.
2. **A longer run still buys the most here, and both runners are already fast.** Their accelerated runners take
   frames in closed-form jumps, so the number of frames grows like the square of the compute: ten times the
   compute is 6.6 doublings, about +0.3 to +0.4 expected hits per machine. (Done on 27 November for
   1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD: 6·10^12 passes, 2.4·10^37 machine steps, no halt, one more zigzag
   start one cell from a halting row.) For
   1RB1RF_0LC0RF_1RD1LC_---0LE_0RC1LF_1RA0LE that is about 6 core-days at the measured 10 ns per rule
   (`c/rounds.c`); for 1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD about one core-day (`c/crun`). The runs are one
   orbit each and cannot be split across cores.
3. **The other five are not worth hunting.** Their rates are a hundred times lower and drop further when the
   copies keep the orbit's parities: about a thousand doublings per expected hit. For
   1RB1RF_1LC1LF_0RE1LD_0LB1LD_---1RC_1RA0RD this matches what its folder already says (odd stretches cannot
   halt). For the four `1RB1RD_0LC1RA...` and `1RB1LE_1RC1RA...` machines it says the same as the residue search of
   [`residue-closed-sets-nov26.md`](residue-closed-sets-nov26.md) from the other side: no closed set of residues
   exists, but a halt is also not to be expected by running.

## Machines of section E that the probe cannot take

| machines | why | what their folders say |
|---|---|---|
| 1RB0LA_0RC0RB_1LD1LA_1LC1RE_1RF0RD_1LC--- and the rest of the Vampire family | a run is under way in another thread | a halt reported near 7·10^11 passes |
| 1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE, 1RB1LC_1RC0LD_1LA0RB_1LB1LE_1RF0LA_---0RE, 1RB1RE_1LC0RA_1RD0LB_1LB1RC_1LF0RD_---0LE | the value grows about 1.58 times per round, so it leaves 63 bits after 90 rounds | the chance of a hit is about 2^−k per round at level k, and k grows linearly: the sum converges, and what is left after the 10^5 rounds already run is about 10^−20,000. Do not hunt. |
| 1RB1LE_1RC1LF_0RD1RD_1LE0RE_0LA0LB_---1LE, 1RB1RE_1LC0RF_1LA0LD_1LE1LC_0RA0LC_1RA--- | the state is a list of timers of growing length, not a fixed number of counts | run to 10^70,169 steps for the second; of 300 random tapes of its shape, 22 halt within 10^150 steps |

## What the tool is, in one paragraph

A visit map is written as a list of cases (`tools/segreplay/specs/`; `lean2spec.py` makes it from a Lean
`Phases.lean`). From it `segreplay.py` writes a Coq file with the map on integers, the map on 63-bit machine
integers and a generated proof that they agree, a C runner that proposes segment end points, and one Coq file
per segment. Coq then recomputes every segment and chains them into "the orbit halts at visit N" or "no halt in
the first N visits". Eight maps go through with no hand work, 66 and 78 cases for the largest. As a test, the
last 59,656,218,975 visits of the halting orbit of 1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC were replayed
this way (12 segments, 3 minutes each) and joined to the map of the busycoq proof
(`tools/segreplay/examples/`). Plain replay costs about 40 to 100 ns per visit in Coq, so it reaches 10^12 visits
comfortably and 10^13 with patience; beyond that a machine needs its own block step, which the runner accepts.

## Suggested next steps

1. Extend the two runs of point 2 tenfold. Together that is about a week of one core each and +0.7 expected
   hits at face value.
2. For the same two machines, look for what the orbit keeps that its neighbours do not, starting from the
   merging: describe the states of the merged orbits (what a state looks like long after its last reset case)
   and ask whether the halting cases can be reached from them. The probe can be pointed
   at any candidate: move the copies only in ways that keep it, and see whether the halting rate drops.
3. If a halt is found, the replay needs a block step for that map (as `Block.v` is for the calibration machine),
   since 2^83 frames one at a time is out of reach.
