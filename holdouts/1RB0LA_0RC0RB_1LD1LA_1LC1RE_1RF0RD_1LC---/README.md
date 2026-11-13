# 1RB0LA_0RC0RB_1LD1LA_1LC1RE_1RF0RD_1LC---

bbchallenge id 121010. Group G01. **3/2-Collatz with a counter-like context word**: a number n is multiplied by about
3/2 per pass, and a short word on the left of the tape, rewritten after each pass according to n mod 4, behaves
like a binary counter; two words halt (`11111`, `1111011` with ⌈n/2⌉ odd). Open; probviously halting, after
about 10¹² passes; no halt in the first 4.3·10⁹ passes (2^18 of them proved in Lean).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LA |
| B | 0RC | 0RB |
| C | 1LD | 1LA |
| D | 1LC | 1RE |
| E | 1RF | 0RD |
| F | 1LC | --- |

## What it does

Sample the run at an **E-event**: the head, in state E, enters the last run of 1s from the left,

    c E> 1^n        (blank beyond)

with `c` (the tape from its first 1 up to the head) the *context*. From blank tape the first E-event is (c, n) =
(`1`, 19) at step 153. The next E-event is

    (c, n)  ->  (c', (3n + δ)/2),    c' = f(c, b),  b = ⌈n/2⌉ mod 2,   δ = δ(c, n mod 4)

### Derived from the machine (second pass)

The map is now derived from the table, not measured, and proved in Lean for every n:

1. **The E-pass halves the block.** E1→0RD, D1→1RE turn `1^n` into `(01)^k` with k = ⌈n/2⌉; then F/C put
   `1 1` at the end: the head is in C on the first cell of a block of 2 (`epass_even`, `epass_odd`).
2. **Every two `01` become six 1s** (`pairs`, iterated in `loop`): C steps left, A turns the nearest 1 into 0, B
   erases the block to its end (B1 → 0RB), and C/D sweep back left writing 1s two cells further. After the
   halving the context has a block of **m = 3k + 2** ones, and if k is odd one extra 1 is appended to the context
   (`pass0`..`pass3`). This part is the same for **every** context: `n ≡ 0: 6⌊n/4⌋+2`, `1, 2: 6⌊n/4⌋+5` (context
   gets a 1), `3: 6⌊n/4⌋+8`.
3. **The context is then rewritten as a binary counter read from the right.** With the head in C on the block
   (`w C> 1^m`), C1 → 1LA and A (A1 → 0LA, A0 → 1RB) *adds one to w read as a binary number* (least significant
   bit next to the head); B then erases to the next 0 and C/D refill leftwards, which either feeds the last bit of
   w into the block (three more 1s) or, when the refill arrives in D on a 1, starts the next E-pass (D1 → 1RE). The
   local rules, for every prefix u:

   | end of w | m even | m odd |
   |---|---|---|
   | `u0` | `u`, m+3 | E-event (`u1`, m+2) |
   | `u01` | `u10`, m (an increment) | `u10`, m |
   | `u011` | `u`, m+3 | `u`, m+3 (`r_zoo`) |
   | `u0111…` | longer carries; three or more 1s in a row can make an E-pass start on a short inner run, which is how F1 (the halt) is reached | |

   Only the parity of m matters, so c' depends on c and b only, and the context adds a constant number a_b(c)
   of ones: δ(c, 0) = 4 + 2a₀, δ(c, 3) = 7 + 2a₀, δ(c, 2) = 4 + 2a₁, δ(c, 1) = 7 + 2a₁ (`nextE` in
   `lean/Orbit.lean`). Each context's rewrite takes only a few sweeps, linear in m (e.g. 8j + 56 steps for context `1` with b = 1, block 2j + 5).

**The context is not a finite-state counter.** The contexts reachable from `1` (over all bit sequences) grow
exponentially with their length: 163 of length ≤ 12, 689 of length ≤ 16, 7,775 of length ≤ 20. So no finite table
of contexts is closed; the uniform description is the rewriting above (a binary-increment transducer on the right
end of the context) plus the context-independent arithmetic of step 2. Along alternating bits 0101… the context
counts up in a mixed radix (a top digit `1`/`11`, then digits `000`, `001`, `011`, then `0001`):
`1, 10001, 110001, 10000001, 10010001, 10110001, 110000001, …`; other bit pairs make it fall back.

### The halting condition

The machine halts exactly when an E-event (c, n) has a halting rule: the context's rewrite starts an E-pass on an
inner run whose end is followed by `0 1`, so F reads a 1. Among all contexts the Markov model can reach with
non-negligible weight, only two rules matter:

* `11111` with b = 1 (61 % of the halting rate),
* `1111011` with b = 1 (39 %).

Lean (`halts_of_orbit`) proves that reaching either one, with ⌈n/2⌉ odd, halts the machine. The shortest bit
sequence from `1` to a halt has 42 passes (`0101…0110010101`): the counter has to count up to `10110110001`
without an error and then take a specific exit.

### Is the halting rate really per pass? (the heuristic, re-examined)

Yes. n' = (3n + δ)/2 with δ fixed by (c, n mod 4), so n mod 2^(k+1) determines the next k bits, and every one of
the 2^k bit strings comes from exactly two residues mod 2^(k+1), whatever the context (checked for k = 12 from four
contexts, `py/markov.py bits 12`; it is the usual Collatz parity-vector bijection). The bit used at pass i is a bit
of n₀'s 2-adic expansion that no earlier pass read; the size of n never enters (n grows by 0.585 bits per pass but
one fresh low bit is consumed per pass). There is no shrinking factor: halting needs a specific ~42-bit pattern
somewhere in an infinite stream of fresh bits.

So the context is a Markov chain driven by fair bits. Its quasi-stationary distribution agrees with the actual orbit
to four digits (`1`: 0.34574 model vs 0.34575 orbit over 2^32 passes; `11`: 0.29769 vs 0.29770; `1111`: 1.0148·10⁻⁴
vs 1.0124·10⁻⁴; `1110001`: 1.0002·10⁻⁵ vs 0.9958·10⁻⁵), and its absorption rate is **8.87·10⁻¹³ per pass**
(mean 1.13·10¹² passes; `py/markov.py rate 400`). The context `11111` itself has stationary probability 1.1·10⁻¹².
The chance of a halt within the 4.3·10⁹ passes checked below is 0.4 %; none happened.

**Probviously halting**, after about 10¹² passes, i.e. with n of about 2.5·10¹¹ bits and a step count of roughly
10^(7·10¹⁰). Far beyond any computation: the iteration below is memory-bound at about 2^33 passes.

### Iterating the map far

`c/orbit.c` iterates the map by divide and conquer on the low bits of n (k passes need only n mod 2^(k+1); the
halves are combined as n_k = (3^k n + B_k)/2^k with GMP), O(M(K) log K) instead of O(K²):

| passes | time | result |
|---|---|---|
| 2^20 | 0.1 s | equal to plain big-integer iteration with `py/rules.json` (`py/orbit_check.py`: same final context, bit length 613,383 and n mod 2^64) |
| 2^30 = 1.07·10⁹ | 3 min | no halt; 55 contexts, longest 11 cells |
| 2^32 = 4.29·10⁹ | 18 min, 2.4 GB | no halt; 65 contexts, longest 11 cells; n then has 2.5·10⁹ bits |

## What is proved

| level | result | where |
|---|---|---|
| kernel | the halting configurations; no halt in 10⁴ steps | `lean/Blank.lean` (generated) |
| native | no halt in 10⁷ steps | `lean/Blank.lean` |
| kernel | the E-pass for every context P and every n: `P E> 1^n` reaches `P C> 1^(3⌈n/2⌉+2)` or `P 1 C> 1^(3⌈n/2⌉+2)` | `pass0`..`pass3`, `lean/Pass.lean` (pieces from `lean/Rules.lean`) |
| kernel | the rewrite of each of the 55 contexts the orbit uses in 2^30 passes, both bits, for every block length: 110 rules (c, b) → (c', a) | `ctx_k_b`, `tbl_sound`, `lean/Ctx.lean` |
| kernel | the map: `nextE c n` is reached from `Ev c n` for every n ≥ 6 and every table context | `nextE_sound`, `lean/Orbit.lean` |
| kernel | blank tape reaches (`1`, 19) at step 153 | `blank_reaches_E` |
| kernel | 10,000 passes stay in the table: no halt in the first 10^1700 steps | `orbit_kernel`, `no_halt_kernel`, `kernel_bound` |
| native | 2^18 = 262,144 passes: no halt in the first 10^45000 steps (2^22 passes also check, in 29 min) | `orbit_native`, `no_halt_native`, `native_bound` |
| kernel | reaching `11111` or `1111011` with ⌈n/2⌉ odd halts the machine; staying in the table forever means no halt | `halts_of_orbit`, `halt_11111_1`, `halt_1111011_1`, `not_halts_of_forall` |
| trusted | 2^32 = 4.29·10⁹ passes without a halt (n reaches 2.5·10⁹ bits) | `c/orbit.c 32` |
| heuristic | fair bits (proved bijection); Markov rate 8.87·10⁻¹³ per pass, halt after ~1.1·10¹² passes | `py/markov.py` |

## Reproduce

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LA_0RC0RB_1LD1LA_1LC1RE_1RF0RD_1LC---/lean/check.sh   # about 1 min
cd holdouts/1RB0LA_0RC0RB_1LD1LA_1LC1RE_1RF0RD_1LC---
python3 py/leanrules.py > lean/Rules.lean         # the context-independent pieces (symtm)
python3 py/leanctx.py > lean/Ctx.lean             # the 110 context rewrites and the 2 halting ones (symtm)
gcc -O2 -o orbit c/orbit.c -l:libgmp.so.10        # (or -DHAVE_GMP_H -lgmp with gmp.h installed)
./orbit 20 check; python3 py/orbit_check.py 1048576   # the two must agree
./orbit 30                                        # 2^30 passes, 3 min
python3 py/markov.py rate 400                     # halting rate, halting rules, stationary distribution
python3 py/markov.py bits 12                      # the bijection n mod 2^13 -> 12 bits
python3 py/emap.py path                           # the shortest path to a halt
```

`py/contexts.txt` lists the contexts of the 2^30 run (the Lean table). `py/g01tools.py` and `c/from.c` are shared
helpers used by the other G01 folders too.

## Further work

- A Lean proof of the context rewrite for *every* context would need the binary-increment transducer of step 3 as a
  recursive function with a soundness proof by induction on the context; the rules for runs of three or more 1s
  (where the head carries over an inner block) are the hard part.
- Nothing short of ~10¹² passes is expected to settle it; beyond 2^33 passes the low bits of n alone exceed memory.
- The sibling `1RB0LA_0RC0RB_1LD1LA_1LC1RE_1RF0RD_1LA---` differs in F0 (1LA instead of 1LC).

## Remainder classes (family survey)

- **Rounds between end events, by remainder class** (trusted). Sample the run whenever the head is in state D reading 0 with only 0s to its right. Read leftwards from the head, the tape is then `A U^m B`: one long periodic block between two short context words. For each class (A, U, B, m mod 2) the next sample is simulated for six values of m and extended as an affine map of m (with a cubic step count). Along the direct run from blank tape to 3·10^9 steps (21 events) the class map predicts the next event in all 15 rounds it applies to. This is an extrapolation checked by computation, not a proof. Command: `python3 holdouts/1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---/py/ctxround.py 1RB0LA_0RC0RB_1LD1LA_1LC1RE_1RF0RD_1LC--- R D 0 check 3e9`
- **285,323 rounds of the class map without a halt** (heuristic). Iterated with exact integers from the event at step 8,732 of the run (A = `0`, U = `01`, m = 82, B = `(empty)`): 285,323 rounds without meeting a halting class; m then has 169,300 bits (about 10^101,928 steps of the machine). 30 distinct contexts occur, the longest of 9 cells. Command: `python3 holdouts/1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---/py/ctxround.py 1RB0LA_0RC0RB_1LD1LA_1LC1RE_1RF0RD_1LC--- R D 0 orbit 285323`
- **Some remainder classes halt** (heuristic). Breadth first from the starting context, with every remainder at every context (whether or not the numbers can really produce that sequence of remainders, and only for m large compared with the contexts): 5,000 contexts expanded, 5,014 found, to depth 922. **85 classes halt.** The nearest one is reached by the remainders 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1^3 0 1^3 0 1^3 (42 rounds, moduli as above), ending at B = `1^4`. Command: `python3 holdouts/1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---/py/ctxround.py 1RB0LA_0RC0RB_1LD1LA_1LC1RE_1RF0RD_1LC--- R D 0 bfs 5000`

## Pages

- [`pages/holdouts/1RB0LA_0RC0RB_1LD1LA_1LC1RE_1RF0RD_1LC---/explainer.html`](../../pages/holdouts/1RB0LA_0RC0RB_1LD1LA_1LC1RE_1RF0RD_1LC---/explainer.html)
- [`pages/holdouts/1RB0LA_0RC0RB_1LD1LA_1LC1RE_1RF0RD_1LC---/proof-status.html`](../../pages/holdouts/1RB0LA_0RC0RB_1LD1LA_1LC1RE_1RF0RD_1LC---/proof-status.html)

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0RF_1LC---_1LF1LD_1RE0LD_0RC0RE_1LC1RA`](../1RB0RF_1LC---_1LF1LD_1RE0LD_0RC0RE_1LC1RA/README.md): rename A→D, B→E, C→C, D→F, E→A, F→B; it is this table started in state E

<!-- end of related machines -->
