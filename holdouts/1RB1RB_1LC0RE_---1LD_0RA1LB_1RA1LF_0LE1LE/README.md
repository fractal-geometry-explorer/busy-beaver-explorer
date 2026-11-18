# 1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE

bbchallenge id 159080. One of the six-state holdouts whose halting from blank tape is open.

**What it does, in one line:** two blocks of 1s, of lengths `2i` and `2j`, play a game like Euclid's algorithm
with tripling: each round the shorter block is (about) tripled and taken off the longer one,
`(i, j) -> (i - j - 1, 3j + 2)` or `(j - i - 2, 3i + 3)` and so on, and the machine halts exactly when the two
blocks come out the same size (`i = j`) or off by one (`i + 1 = j`). Lean proves this reduction (kernel only):
the machine halts from blank tape **iff** the orbit of `(3, 1, R1)` under the map below ever reaches such a pair.
The orbit has been iterated for 10^6 rounds (to numbers of about 92,000 digits) without that happening;
whether it ever does is a Collatz-like open question, with a vanishing chance of halting (a "probviously
non-halting" cryptid).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RB |
| B | 1LC | 0RE |
| C | --- | 1LD |
| D | 0RA | 1LB |
| E | 1RA | 1LF |
| F | 0LE | 1LE |


## The round

At the start of each round the head is at the right end of the tape in state B, and the tape is one of

    R1(i, j) = 0^∞ 1^(2i) 0 1^(2j) 0 11 B> 0^∞
    R2(i, j) = 0^∞ 1^(2i) 0 1^(2j) 0 11 0 11 B> 0^∞

(the short tail `0 11` or `0 11 0 11` is a one-bit flag `J`, 0 for R1, 1 for R2). The head runs left to the left
end, where the round becomes a *three-block bouncer*

    K3(a, b, c) = 0^∞ E> 0 1^a 0 1^b 0 1^c 0^∞        (a = 2i, b = 2j - 3, c = 6 after R1, 9 after R2)

A four-cell zig-zag `0110` (the *carrier*) walks right across the first two blocks, turns at the third, and the
head comes back in states E/F: one such pass takes `(a, b, c)` to `(a - 2, b - 2, c + 6)` and moves the left end
of the tape two cells out (`pass`, `passes` in Lean, by induction on the number of passes). The passes go on until
`a = 2` or `b = 1`; then the round ends in one of a few ways, all proved for every value of the counts. In the
half-lengths `(i, j)` and the flag `J`, the round map is (`next` in `lean/Round.lean`):

| case | J = 0 (R1) | J = 1 (R2) |
|---|---|---|
| `i >= j + 2` | `(i - j - 1, 3j + 2, 0)` | `(i - j - 1, 3j + 3, 1)` |
| `i = j + 1` | `(3i - 3, 3, 1)` | `(3i, 1, 0)` |
| `i = j` or `i + 1 = j` | **halts** | **halts** |
| `i + 2 = j` | `(3i + 3, 1, 0)` | `(3i + 3, 3, 1)` |
| `i + 3 <= j` | `(j - i - 2, 3i + 3, 1)` | `(j - i - 2, 3i + 5, 0)` |

The parity of the third block `c` decides which tail the next round has, which is why the flag flips when the
order of the two blocks flips. From blank tape the first round starts at step 74 in `R1(3, 1)`; the orbit begins

    (3,1,0) (1,5,0) (2,6,1) (2,11,0) (7,9,1) (24,3,1) (20,12,1) (7,39,1) (30,26,0) (3,80,0) (75,12,1) ...

## The recursion in rule form

Exact tapes, then one rule per case of `next` with the exact number of machine steps of the round, as the
bbchallenge wiki writes Antihydra's (i ≥ 1, j ≥ 1, and j ≥ 2 for R2):

    R1(i, j) := 0^∞ 1^(2i) 0 1^(2j) 0 11 B> 0^∞
    R2(i, j) := 0^∞ 1^(2i) 0 1^(2j) 0 11 0 11 B> 0^∞

    0^∞ A> 0^∞     --74-->                   R1(3, 1)
    R1(i, j)       --12ij + 24j + 11-->      R1(i − j − 1, 3j + 2)       i ≥ j + 2
    R2(i, j)       --12ij + 24j + 27-->      R2(i − j − 1, 3j + 3)       i ≥ j + 2
    R1(j + 1, j)   --12j² + 72j + 50-->      R2(3j, 3)
    R2(j + 1, j)   --12j² + 36j + 27-->      R1(3j + 3, 1)
    R1(j, j)       --12j² − 6j + 5-->        HALT
    R2(j, j)       --12j² − 6j + 8-->        HALT
    R1(j − 1, j)   --12j² − 18j + 14-->      HALT
    R2(j − 1, j)   --12j² − 18j + 17-->      HALT
    R1(j − 2, j)   --12j² − 9-->             R1(3j − 3, 1)
    R2(j − 2, j)   --12j² + 36j + 14-->      R2(3j − 3, 3)
    R1(i, j)       --12ij + 12i + 12j + 15-->  R2(j − i − 2, 3i + 3)     i + 3 ≤ j
    R2(i, j)       --12ij + 12i + 12j + 35-->  R1(j − i − 2, 3i + 5)     i + 3 ≤ j

The rules are `next` of `lean/Round.lean`, proved (`round_ok`), with the halts-iff (`halts_iff`) and the start
(`init_reach`, 74 steps). The step counts are proved for the pieces of a round (`lean/Pieces.lean`: start
2i + 2j + 13 or + 16, inner pass 12p + 12q + 50 (`inner_e`), the ends and halts); `Round.lean` joins them with `Reach`, which
drops the counts, so the totals are sums of proved counts, checked against direct simulation (`py/orbit.py rules`:
all 3,160 rounds with i, j ≤ 40, 157 halting, target and steps; all 23 round starts of the first 10^7 steps from
blank tape), not stated in Lean. Halt rows count the halting transition. Example: R1(4, 8) → R2(2, 15) (543)
→ R1(11, 11) (599) → halt (1,391): 2,533 steps, as in direct simulation. (The wiki page cuts the round elsewhere,
with a family C(a, c, f) and no step counts.)

## Emergent behaviour

* **What is counted.** Two numbers, the lengths of the two blocks of 1s. A round subtracts the smaller from the
  larger and puts back three times the smaller: a Euclid-like subtraction game in which the numbers keep growing
  (by a factor of about 2^0.31 per round on average along the orbit).
* **The two sides of the tape.** The left end moves out two cells per inner pass, and the number of passes is
  the size of the smaller block, so the left side grows like the square root of the step count (each round costs
  about the square of the block sizes in steps). The right end moves by one or three cells per round (the tail
  `0 11` / `0 11 0 11`), and the number of rounds grows like the logarithm of the step count: that is the
  log side.
* **Halting.** The machine halts exactly when the two blocks run out together, `i - j` in `{0, -1}`: then the
  carrier meets a blank where it expects the third block and the head reads a 0 in state C (C0 is the halting
  transition). Along the orbit `i - j` behaves like a random number of the size of `i` and `j`, so the chance of
  hitting `{0, -1}` in a round with `n`-bit numbers is about `2^-n`; the expected number of future hits is
  astronomically small. Proving that it never happens is a problem of the Collatz type (the map mixes
  subtraction with multiplication by 3), and no invariant is known that rules it out: residues alone cannot,
  since `i - j = 0` is only excluded by size, not by any congruence.

## Status

**Open (probviously non-halting).**

* Kernel (Lean, `lean/Round.lean`, no `native_decide`): `halts_iff : HaltsFromBlank ↔ ∃ n, orb n = none`,
  where `orb` iterates `next` from `(3, 1, false)`. This rests on `round_ok` (every round, for all values of
  `i, j`, does what `next` says, or halts when `next` is `none`), built from 26 symbolic runs in
  `lean/Pieces.lean` (generated by `py/gen_pieces.py` with `bbtools.symtm`) and the induction `passes`.
* Computed: the first rounds of the real machine agree with the map (`py/orbit.py check 22` in Python; the C
  simulator's round starts up to 3·10^10 steps, 46 rounds); the map iterated for 10^6 rounds
  (`py/orbit.py iterate`) never reaches a halting pair. Closest approach (relative): round 547,658, where `i - j` still has 167,823 bits against 167,848 for `i` and `j`.
* From the generated folder: Lean (`lean/Blank.lean`) no halt in 10,000 steps by the kernel, 10^7 by
  `native_decide`; C (`tools/c/triage.c`) no halt in 10^9 steps.

### For later

The open question is now purely about the map `next`. To close it one would need a reason why `i - j` never
lands in `{0, -1}`: for instance a 2-adic or base-3 description of the orbit (the map is piecewise affine with
multiplier 3 on one coordinate), or a proof that a halting pair has no predecessor reachable from `(3, 1, 0)`.
Backward search from the halting pairs (the map is injective on each piece, so preimages are easy to list) is the
natural next experiment.

## Long orbit run (16 November 2026)

`tools/c/redmaps.c rb` iterates `next` of `lean/Round.lean` from (3, 1, false) with GMP integers, case by case as in the
Lean definition (its first 30,000 iterates equal those of `py/orbit.py`). **2·10^7 rounds** (20 times the earlier run),
about 25 minutes on one core: the orbit never reaches i = j or i + 1 = j. After 2·10^7 rounds the two numbers of
(i, j) have 6,127,225 and 6,127,223 bits; over rounds 1,000 to 2·10^7 the halting difference i − j never came closer than
26 bits below the size of the numbers (round 1,000,578). Computed (trusted), not in Lean.

    gcc -O2 -o redmaps tools/c/redmaps.c -l:libgmp.so.10 && ./redmaps rb 20000000 1000000 rb.ck

## Pages

- [`pages/holdouts/1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE/explainer.html`](../../pages/holdouts/1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE/explainer.html)
- [`pages/holdouts/1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE/proof-status.html`](../../pages/holdouts/1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE/lean/check.sh
cd holdouts/1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE
python3 py/orbit.py check 22            # the first rounds of the machine against the map
python3 py/orbit.py rules               # the rule table and its step counts against direct simulation
```
