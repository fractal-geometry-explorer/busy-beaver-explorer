# Independent check of the closed-set certificate (machine 11019)

Machine `1RB0RD_1RC0LF_1LA0LB_---1RE_1LB1RA_0LC0RA`. Checked: `../py/closure/cert.json` (1,144 classes).
Date: 13 Nov 2026. Checker: a separate worker; the engine code `py/closure/accel.py` and `closure.py` was not
read or used. From the notes only the conventions were taken (node layout, meaning of the certificate fields).

**Result: the claim was NOT refuted. Every test agrees with the certificate exactly; 0 mismatches.**
What this does and does not establish is in the last section.

## Conventions used
- Node: state A, head on the first cell of `01001000 (01)^B T`, every cell to the left of the head blank,
  nothing but blanks after T. Test used by both tools: state A, all blank on the left, the eight cells from
  the head on read `01001000`; then B = the longest run of `01` that follows, T = the rest up to the last 1.
  "Next node" = the first such configuration at a step > 0, whatever its B and T (stricter than "some node").
- Class = (tail, r, m): all B >= 20000 with B = r mod m, written B = r0 + m x. Certificate says: the next node
  has tail `to`, B' = k + c x, and comes after steps[0] + steps[1] x + steps[2] x^2 steps.
- HALT n = n steps were executed and the next transition is the undefined one (D reading 0).

## Tools (all written for this check)
- `plain.cpp` (46 lines): cell-by-cell simulation, one byte per cell. The ground truth.
- `accel.cpp` (306 lines): exact accelerated simulator. Tape = runs of K-cell words (default K = 6) plus one
  "back" block behind the head. A block step is a plain simulation confined to two blocks; if the head leaves
  in front in the same state with the same back block, the whole run is crossed at once. Cycle jump: when the
  shape of the tape recurs, the stretch in between is re-simulated with every large count as "variable +
  offset"; all decisions of the engine then depend on the shape alone as long as each variable run keeps
  count >= 2, which gives a lower bound per count. The rule "shape(n) -> shape(n + d), s0 + sum s_v n_v steps,
  no halt, no node" is applied N times, N the largest number keeping every count above its bound; steps are
  summed exactly (128-bit). No chain step or jump can skip a node: the leftmost block is always done cell by
  cell with the node test at every step, and a period that meets the test prefix is never turned into a rule.
  The re-simulation is asserted equal to the real run (tape, steps, operation count) before any jump.
- `check.py`: reads the certificate, builds the members, compares. `run_all.sh`: everything; `run_all.log`: output.

## How to run
    bash run_all.sh         # 1.6 min on one core; binaries go to $VBIN (default /tmp/claude-0/g09/verify11019)
    bash run_all.sh full    # adds 14 classes at B ~ 20000 by plain simulation (5 more minutes)

## What was checked, with exact results
1. **Arrival from blank.** `plain` from the blank tape: nodes at B = 2, 12, 13, 21, 55, 103, 255, 586, 1291,
   2827, 6280, 12967 and then **B = 28531 at step 2,340,515,329**, tail
   `0000101010101010100001010101010101000010000101010101010101010101010101010101011101` = `start.tail`
   of the certificate, which is a listed class (B >= 20000). `accel` (K = 6, K = 12, jumps off) prints the same
   13 lines. CONFIRMED.
2. **Simulator against plain simulation.** 400 tapes with B in 3..299 and 150 tapes with B in 300..2499 (tails
   of the set, tails with one block changed, one cell flipped, random tails): 472 reach a node, 78 halt; step,
   B and tail identical between `plain` and `accel` under 8 option sets (K = 2, 4, 6, 8, 12, 18; thresholds for
   "large" 4 to 64; jumps on and off; 439 cycle jumps in total). 14 randomly drawn classes at x = 0 (B ~ 20000, 4.1e9 to
   4.4e9 steps each) by `plain`: step, B', tail equal to the certificate and to `accel`, 14 of 14.
3. **Every class.** For each of the 1,144 classes four members: x = 0 (least B >= 20000), x = 1, one with B
   between 10^6 and 10^7, one with B between 10^11 and 10^12. Next node: no halt, step count, B' and tail
   exactly as the certificate says, and (tail, B') in a listed class: **4,576 of 4,576, 0 mismatches**. Repeated
   with K = 12, with threshold 500, with K = 18 / threshold 20: 0 mismatches each. All classes at x = 0 and 1
   again with cycle jumps switched off (chain steps only): 2,288 of 2,288.
4. **Random members.** 2,000 random (class, B < 10^9): 0 mismatches; a second 2,000 with another seed and
   K = 12: 0 mismatches. 3,000 random (class, x in 2..199): 0 mismatches.
5. **The real run.** From the start node, 39 consecutive rounds (B from 28531 to 1.9e17, 1.1e35 steps): each
   node is in the class the certificate predicts, steps exact. 0 mismatches.
6. **Certificate as a table.** 1,144 distinct classes, 62 tails, one modulus per tail (66: 682 classes, 45: 300,
   48: 144, 27: 18), r0 correct, least k = 41224 >= 20000; for every class every residue of k + c j modulo the
   target tail's modulus is listed. 0 problems.
7. **Halting neighbours.** The 5 tails of the notes ("halt for every B = 1 mod 3"), with B = 20002 + 3x: `accel`
   halts at exactly a + b x for x = 0, 1, 3, 1000, 333333, 10^8 (a, b as in the notes: 574239+86x, 816931+122x,
   817189+122x, 815565+122x, 575879+86x); `plain` halts at the same step for x = 0, 1, 3. None of the 5 tails
   is in the certificate. So both tools do report halting, and tapes of the same shape do halt.
8. **The comparison is not vacuous.** 30 classes with k, c, a step coefficient or the target tail altered:
   30 of 30 reported.

## What this check does NOT establish
- It samples B. Per class 4 fixed members were run, plus 7,000 random members and 39 rounds of the real run
  (each an exact simulation). That every B of a class behaves as the formula says rests on the symbolic run of
  `py/closure`, which was not examined here. A class that fails only for B in some rare residue or beyond
  10^12 would not be seen. (Agreement of a quadratic step count and a linear B' at 4+ points per class, for
  all 1,144 classes, makes a wrong formula unlikely, but that is evidence, not proof.)
- `accel.cpp` is itself an unverified program. It agrees with plain simulation wherever plain simulation is
  feasible (up to 4.4e9 steps), and its results do not change with K or the threshold; for B >= 10^6 there
  is no plain-simulation ground truth, only that agreement.
- No machine-checked proof. The status of the machine stays what it was: closed set found and independently
  sampled, not proven.
