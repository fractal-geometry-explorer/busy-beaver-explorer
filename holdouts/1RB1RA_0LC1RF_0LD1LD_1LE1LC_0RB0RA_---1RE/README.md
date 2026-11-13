# 1RB1RA_0LC1RF_0LD1LD_1LE1LC_0RB0RA_---1RE

bbchallenge id 41677. A BB(6) holdout whose halting from blank tape is open. Family: **block list with a 4v+3
carry**. Decision: **open** (reduced, in Lean, to a question about a rule on lists of numbers).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RA |
| B | 0LC | 1RF |
| C | 0LD | 1LD |
| D | 1LE | 1LC |
| E | 0RB | 0RA |
| F | --- | 1RE |

## The machine is a block-list system (proved)

Look at the tape at each visit of the right end in state B (`B> 0^inf`). It is a list of blocks of 1s, each followed
by one 0, `b0 0 b1 0 ... 0 z B>` (a block may be empty: two 0s in a row; blank tape left of the first block counts
as empty blocks). One sweep (the run to the next such visit) is this rule, `sweep` in `lean/Macro.lean`
(`step` in `py/blocks.py`, front block first):

* **target.** The head runs left in C over z and in C/D over the blocks before it: it passes z if z is even and then
  every odd block. The target is z if z is odd, otherwise the last even block e before z.
* **turn.** Let x be the block left of the target. If x ≥ 1, x loses one 1 and the target gains 4 (z gains 2 when
  z is the target). If x is empty (or the target is the first block), x becomes a new block 2 and the target gains
  1 (z loses 1 when z is the target).
* **back.** Every odd block between the target and z keeps its length (it hands three 1s to the block before it and
  takes its separator); z loses 2. If z was empty, it disappears and the block before it loses 2.
* **halts** (F reads 0) exactly when: z is even and there is no even block before it (the head reaches the left
  end in C); an odd block of length 1 lies between the target and z (or is the block before an empty z); or the
  target is an empty block after an empty block.

Theorem `visit` (Lean, kernel): for **every** block list on which `sweep` is defined, the machine goes from that
tape to the tape of the result in at least one step. Theorem `nonhalt_of_orbit`: if the orbit of `[1]` (the tape
after the first step) under `sweep` is defined for ever, the machine never halts from blank tape. The proof is by
hand from the shift-rule lemmas of the shared library (`cross_l`, `cross_r`) and induction over the list: a lemma for
passing an odd block leftwards, one for reaching an even block, one per case of the turn, and the cascade back by
induction over the blocks passed.

Each sweep costs 2D + 5 steps (2D + 4 when an empty z disappears), D the number of cells from the target block to the
right end (`py/fastrun.py`, checked against the machine).

## What the rule does (emergent behaviour)

* **The carry.** Almost always the target is a *carry* just right of a block x: each visit it takes one 1 from x and
  gains 4, while z pays 2. When x is empty, x becomes a new carry 2 and the old carry has length 2 + 4x + 1 = 4x + 3.
  So a pass of the carry moves each block one place right and maps its length v to **4v + 3**:
  3 → 15 → 63 → 255 → 1023 → … At the left end the blank tape is a supply of empty blocks and the carry creates a new
  3 at each visit. Hence the long runs of blocks of length 4^k − 1, each pass moving every run one level up:

      visit ~10^7   2 3*21508 11 15*828 7 34 63*2541 191 255*2097 127 703 1023*194 3071 4095*60 ...
      next pass     2 3*1448893 11 15*21508 47 63*828 31 139 255*2541 767 1023*2097 511 2815 4095*194 ...

  (the glue blocks between runs, 11 → 47, 7 34 → 31 139, follow the same 4v + 3 map).
* **Fuel.** z is the fuel. When it runs out, the last finished block y loses 2 and becomes z (odd), the block w
  before it is poured into z (the odd phase: w loses 1, z gains 2 per visit) and a new carry 2 starts in w's place.
* **Jumps.** If the fuel runs out while the new carry is still next to z, z becomes even (carry + 2) and the next
  target is the last even block further left: the head skips a stretch of odd blocks. This is the only way the target
  moves other than the carry's walk to the left.

## Where a halt could come from

In the carry's ordinary work the blocks between the carry and z are finished blocks 4v + 3 ≥ 3 and the carry is even,
so none of the halting shapes can arise. They can only arise at a jump: a halt needs a block of length 1 in the
skipped stretch (or no even block left of it; but the front block is 2 except while the carry eats it). Blocks of
length 1 do exist: the remainder of a 3 from which a carry had taken two 1s when its fuel ran out, always with the
even carry immediately to its right, which stops any later jump before it. A halt would need a jump to start while
that carry is itself being drained by a new carry and is odd, or a jump leaving a remainder of exactly 1.

Up to 10^1000 steps there are 188 jumps (183 of them skip at least one block); some skip more than 10^19 blocks; the shortest block any jump skips has length 3.

### The coincidence a halt needs (fourth pass)

A refuel leaves `... u x 2 z0` (front first): the new carry 2 next to the fuel z0 (even), x the block it starts to eat.
The carry needs x + 1 visits for x and has z0/2 + 1 (z pays 2 a visit, and one more visit when z is 0). So

* x ≤ z0/2: no jump, the carry eats x and walks on;
* x ≥ z0/2 + 1: a **jump**. When z is 0 the carry (2 + 4F, F = z0/2 + 1) is still next to it and becomes the new
  z = 2 z0 + 4, and x keeps the **remnant r = x − z0/2 − 1**. The target is the last even block before z: r if r is
  even (r = 0 with u = 0 halts), otherwise the head skips r and the odd blocks before it, and the machine halts iff
  r = 1, a skipped block is 1, or no even block is left.

Example: `[2, 3, 3, 11, 2, 18]` (z0 = 18, x = 11, r = 1) halts 10 visits later. So a halt at a jump is an exact equation
between three block lengths, such as x = z0/2 + 2. In the run the remnant is always of the size of the fuel
(`py/jumps.py 2000 300`, exact, to 10^2000 steps): 358 jumps, the smallest remnant is 583 (the first jump), r/F is
never below 2^−9, r mod 8 is spread like a random odd number (v2(r − 1) = 1, 2, 3, ... for about 1/2, 1/4, 1/8, ... of
the jumps) and the sum of 1/r over all jumps is 0.003. The fuel and the eaten block come from different generations of
the carry and show no arithmetic relation, so the heuristic chance of a halt is about the sum of 1/F over the future
jumps; the fuel grows roughly exponentially along the jumps (from 9 bits at the first to 3,315 bits at the 358th),
so this sum is far below 10^−100 for the jumps after 10^2000 steps.

This also says what a proof would have to do: show that x − z0/2 − 1 is never 1 (and the other two shapes never occur)
along the orbit, for lengths with thousands of digits that the rule builds from earlier ones by 4v + 3, sums and
halvings. No congruence forbids it (the remnant takes every residue mod 8), and no inequality keeps r large (r/F
comes within 2^−9). This looks as hard as a Collatz-type question; the size-and-parity invariants tried so far are
too coarse (below).

Parity-and-size abstractions of the list are not enough for a proof: from the reachable-looking shape `[2, 4, 2]` the
rule gives `[1, 8, 0]`, then `[10]`, which halts (no even block before z). Any invariant has to remember that the
fuel is large whenever the carry is close to the front.

## Status

* **Lean (kernel)**: `lean/Macro.lean`: `visit` (the rule is the machine, for every list) and `nonhalt_of_orbit`
  (the reduction).
* **Lean (kernel)**: `lean/Rules.lean` (from `py/rules.py`): the earlier per-case sweep rules for the last four
  blocks and `halt_case` (the local halting pattern), now special cases of `visit`.
* **Lean**: `lean/Blank.lean`: the halting configurations; no halt in 10^4 steps (kernel), 10^7 (`native_decide`).
* **Trusted**: `py/blocks.py`: the rule agrees with a direct run-length simulation of the machine on 20,000 random
  lists and at each of the first 20,000 visits from blank tape (2·10^8 steps); the Python mirror of the Lean
  definition agrees with it on 100,000 random lists.
* **Trusted**: `py/fastrun.py`: the rule with runs of equal blocks as counts and many visits at once, with exact step
  counts (checked against the machine at 200 sample visits up to 10^9 steps): **no halt in 10^4000 steps**
  (about 10^2000 visits, 18,970 fuel exhaustions, 748 jumps).
* **Trusted**: the CTL confinement (windows of 6, `bbtools.ctl`) of F0 to the left end.
* **Trusted**: `py/jumps.py`: the jump remnant r = x − z0/2 − 1 at each of the 358 jumps up to 10^2000 steps
  (smallest 583, r/F ≥ 2^−9, sum of 1/r 0.003).
* **Heuristic**: the jump argument above: a halt needs r = 1 (or one of two similar exact coincidences).
* **Open**: an invariant of `sweep` that excludes the halting shapes; equivalently, that the coincidences above never
  occur.

## Next steps

* A proof of non-halting must show that the jump coincidences never happen. Since the remnant behaves 2-adically like a
  random number and its size relative to the fuel is not bounded away from 0, a proof would need an exact description of
  the orbit's large blocks (their values, not just sizes and parities), which nothing found so far provides.
* A route that would still help: describe the reachable lists outside the jumps exactly (runs `(4^k − 1)^n`, glue
  blocks, carry, fuel) and prove in Lean that every halt of the orbit happens at a jump with r = 1 or the other two shapes;
  that turns the open question into the single equation above, but it does not settle it.
* With any invariant, `nonhalt_of_orbit` turns it into the Lean theorem.

## Pages

- [`pages/holdouts/1RB1RA_0LC1RF_0LD1LD_1LE1LC_0RB0RA_---1RE/explainer.html`](../../pages/holdouts/1RB1RA_0LC1RF_0LD1LD_1LE1LC_0RB0RA_---1RE/explainer.html)
- [`pages/holdouts/1RB1RA_0LC1RF_0LD1LD_1LE1LC_0RB0RA_---1RE/proof-status.html`](../../pages/holdouts/1RB1RA_0LC1RF_0LD1LD_1LE1LC_0RB0RA_---1RE/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RA_0LC1RF_0LD1LD_1LE1LC_0RB0RA_---1RE/lean/check.sh
cd holdouts/1RB1RA_0LC1RF_0LD1LD_1LE1LC_0RB0RA_---1RE/py
python3 blocks.py random 20000 && python3 blocks.py run 20000 && python3 blocks.py lean 100000
python3 fastrun.py check 60000 && python3 fastrun.py far 1000 300
python3 jumps.py 2000 300                                   # every jump: fuel, remnant, skipped stretch
python3 rules.py > ../lean/Rules.lean                       # the earlier per-case rules
cd ../../../tools/py && python3 -m bbtools.ctl 1RB1RA_0LC1RF_0LD1LD_1LE1LC_0RB0RA_---1RE 6
```
