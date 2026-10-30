# Lab notes: 1RB1RA_1RC1LB_1LD0RA_---0LE_1LC0LF_1RE0LB

Newest entries last. Each claim says what it rests on: **Lean** (kernel or `native_decide`), **computed** (a program
in the repository, exhaustive over what it states), or **observed** (a run looked at; evidence, not proof).

## October 29, 2026: setup and first look

**The table.** A0 → 1RB, A1 → 1RA, B0 → 1RC, B1 → 1LB, C0 → 1LD, C1 → 0RA, D0 → halt, D1 → 0LE, E0 → 1LC,
E1 → 0LF, F0 → 1RE, F1 → 0LB. The only halting transition is D0, and D is entered only from C0 (C reading 0, writing
1, moving left). So a halt is C reading a 0, then the cell to its left also a 0.

**Tooling.** The shared tools (`../tools/`) were pulled out of the other machine's code in this session; this
folder uses them as they are. `lean/Machine.lean` is generated from the machine string; `lean/rules.py` writes
`lean/Rules.lean` from the symbolic prover.

**Lean** (`lean/`, `./check.sh`):

- `blank_runs_20000`: no halt in the first 20,000 steps (kernel only, `decide +kernel`, about 10 s).
- `blank_runs_10M`: no halt in the first 10,000,000 steps (`native_decide`, about 10 s).
- `a_sweep`, `b_sweep`: A runs right over any block of ones; B runs left over any block of ones to the 0 before it,
  for every block length and any surrounding tape (kernel only).

**Computed** (`../tools/c/tmrun`, direct simulation, cross-checked against the Python simulator in the tests): no halt
in the first 10¹⁰ steps; 137,072 ones on the tape then.

**Conserved quantities** (`python3 -m bbtools.invariants`, exhaustive over its family): there is no quantity
a·(ones) + b·(head position) + W[state] (mod m) conserved by every transition for any modulus m from 2 to 12. (The
other machine has one mod 3, which the same tool finds.) So the simplest invariant does not help here; richer ones
(over blocks, once the macro rules are known) are next.

**Observed: the tape is a list of blocks.** Read from the run (`tmrun ... records`, `bbtools.explore`): during a
rightward sweep the tape is blocks of ones separated by single 0s, `1^a₁ 0 1^a₂ 0 … 0 1^a_k`; at the moments the head
is at the left end the separators are `00`, with a `000` after the first block:

```
1135     F>0 0^2 1 0^2 1^2 0^2 1^5 0^2 1^7 0^2 1^8 0^2 1^4 0^2 1
14454    B>0 1^14 0^3 1 0^2 1^16 0^2 1^23 0^2 1^38 0^2 1^26 0^2 1^11 0^2 1^4 0^2 1
156814   B>0 1^56 0^3 1 0^2 1^55 0^2 1^104 0^2 1^91 0^2 1^36 0^2 1^35 0^2 1^26 0^2 1^11 0^2 1^4 0^2 1
2023931  B>0 1^192 0^3 1 0^2 1^188 0^2 1^367 0^2 1^200 0^2 …
```

The left end moves out at steps 5, 68, 81, 478, 1,055, 1,122, 1,135, 14,454, 14,611, 156,814, 158,609, 159,054,
2,023,931, 2,043,134, 2,047,931 and then not again up to 10¹⁰ steps. Between the returns the first block roughly halves
(192 → 94 → 45, 56 → 26 → 11, 14 → 5). The head reaches the left end in state F only at steps 5, 81 and 1,135 up to
10¹⁰. The right end grows steadily, with the last blocks cycling through tails like `… 14 5 1`, `… 11 5 1`, `… 13 5 1`,
`… 12 5 1`: a counter of some kind at the right end.

**Next.** Find the block rules (what a sweep does to `a₁ … a_k`), prove them with `rules.py`, and state the macro
step as a map on block lists; then look for the analogue of the other machine's pass starts (here: the head back at the
left end) and what decides whether a sweep can produce C reading `00`.

## October 29, 2026: the macro step, proved

**The macro configuration.** Write `X(ls, n, cs)` for

```
0^∞ 1^{l_r} 0 … 0 1^{l_1} 0 A> 1^n 0 0 0 1^{c_1} 0 0 1^{c_2} … 0 0 1^{c_s} 0^∞
```

with `ls = [l_1, …, l_r]` the blocks left of the head, nearest first, single-0 separated; `n` the block under the head;
`cs` the blocks to the right, `00`-separated, and `000` between the head's block and `c_1`. The run is at
`X([1], 2, [])` after 15 steps, and every later macro configuration has this form. (The configurations at the left
end in the first entry are the special case where B has just come back to the left end of this picture.)

**One macro step** (`next` in `lean/Macro.lean`, `next_step` in `py/macro.py`). Write `bump` for "the first block
gains one (a new block 1 if there is none)".

1. *Transfers* (rule `transfer`, `2n + 11` steps from `n + 2`): `L 0 A> 1^{n+2} 000 R → L 1 0 A> 1^n 000 1 R`: two
   cells of the head's block go, one to `l_1` and one to `c_1`. All `q = ⌊n/2⌋` of them at once take
   `q(2(n mod 2) + 2q + 9)` steps.
2. *n even, the block is empty* (rule `empty_start`, 15 steps): `l_1` gains one and A sweeps right (rule
   `sweep_step`, `m + 3` steps per block: `A> 1^m 0 0 1 R → 1^{m+2} 0 A> R`). Every `00` becomes `0`; `c_1` gains
   4, `c_2 … c_{s-1}` gain 1, and `c_s − 1` becomes the new head's block, with `cs` empty. (With `cs` empty: the new
   state is `X(bump ls, 2, [])`.)
3. *n odd, one cell left*: F carries to the left (rules `carry_start`, `carry_two`, `carry_exit`, `carry_one`).
   Every block equal to 2 that it meets disappears and leaves a `001` on the right (5 steps each). At the first block
   `k ≠ 2` (the `i`-th, after `i` twos):
   * `k ≥ 3`: `X(bump(rest), k − 3, [1]^{i+1} ++ bump(cs))`, a new transfer phase in the middle of the tape;
   * `k = 1`: `bump(rest)`, then a sweep right as in 2, over `[1]^i ++ bump(cs)` starting from a block of 2;
   * no such block (every block to the left is 2): **the machine halts**, 6 steps later (F B C D E C, then D
     reads 0).

So *the machine halts iff some macro configuration has `n` odd and, after `l_1 += ⌊n/2⌋`, every block to the left of
the head equal to 2.* For example `X([2,2,2], 1, cs)` and `X([1], 3, cs)` halt; nothing else does.

**Lean** (`lean/Macro.lean`, `lean/MacroRun.lean`; all kernel-checked except the last):

- the seven rules above, for every block length and any surrounding tape (generated by `rules.py`);
- `next_sound`: from `X ls n cs` the machine reaches the configuration `next` gives, in exactly the steps it gives,
  or halts where it says;
- `next_halt_iff`: a macro step halts iff `n` is odd and every block of `(k + n/2) :: ls` is 2;
- `runM_sound`, `halts_iff`: **the machine halts from blank tape iff the macro run `runM` reaches a halt.** (Every
  reachable macro configuration has a left block and no empty blocks, so `next` never gets stuck, and every macro
  step takes at least one machine step.) The question is now entirely about the list map.
- `runM_1000`: 1,000 macro steps are 1,322,171 machine steps (the same number the Python test checks);
- `blank_runs_2e10`: no halt in the first 2·10¹⁰ steps (10⁵ macro steps by `decide +kernel`, about a minute). This
  replaces the trusted C bound of 10¹⁰ with a kernel-checked one.
- `blank_runs_9e13` (`native_decide`): no halt in the first 9·10¹³ steps (10⁷ macro steps).

**Computed** (`py/macro.py`, tested against the reference simulator: every macro configuration of the first 1,000
macro steps, at the step count the model gives, and the halting branch on built configurations).

**Observed**: in 10⁷ macro steps (9.08·10¹³ machine steps) no macro configuration comes near the halting condition:
the left list holds blocks in the hundreds of thousands. Halting needs the whole left list to be 2s, so it needs the
carry to have eaten everything to the left; the parallel analysis of the left-end returns (`py/waves.py`) studies
exactly when the head gets back to the left end.

**Next.** The halting condition is a statement about the orbit of an explicit list map. Look for an invariant of
`next` that excludes "`n` odd, all 2s", or a coarser description (the other thread's wave recurrence) in which it
becomes arithmetic.

## October 29, 2026: the left-going wave, and why the left end is reached so rarely

**The returns do not stop; the next one is at step 26,618,972,322.** The head reached new tape on the left at
2,047,931 and then not again up to 10¹⁰, but that is just because the next arrival is later. The block-list model
below predicted it at step 26,618,972,322 (with the first block 110,037 cells long), and a direct run to 2.7·10¹⁰ steps
finds exactly that step and no other new left cell in between (**computed**: `tools/c/tm.h`, a twenty-line loop that
prints each new left cell; `WAVES_LONG=1 python3 tests/test_waves.py` repeats it).

**The macro step** (`py/waves.py`, `step`; **computed**: checked against direct simulation). Take as an event the head
in state A on the blank just right of the last block. The tape is then `1^b1 0 1^b2 0 … 0 1^bn A>0` (blocks separated
by single 0s; the last block may be empty), and the next event follows from (b1, …, bn) alone, with an exact step
count. In between, a *wave* runs left from the right end. At each block of length c it does c // 2 *cycles*
(`1^y 0 [B] 1^m 000 1^k → 1^(y+1) 0 [B] 1^(m-2) 000 1^(k+1)`, 2m + 5 steps: the inner loop a route census would
see as an infinite family); then, if c is even, the wave moves on to the block to the left with c' = y + c/2 − 2, and if
c is odd it turns and state A sweeps back right, turning each `00` into `0`. The local rules, each with its step count,
are listed at the top of `waves.py`. The model gives the same block lists at the same steps as `tools/c/tmrun` at every
event of the first 10⁹ steps (12,927 events), and every new left cell in `runs/left_records_1e10.txt`.

**The super step and the number N** (**computed**: checked against four macro steps for 150,000 super steps).
From the second event on, every fourth event has the tape [p1, …, pm, 5, 0], and the next one depends on
P = (p1, …, pm) only. Put d_{m+1} = 20 and d_l = p_l + d_{l+1}/2 for l = m, …, 1. The wave turns at the largest i
with d_i odd, and

    P' = (p1, …, p_{i−2}, p_{i−1} + (d_i − 1)/2, (d_i + 5)/2, d_{i+1}/2, …, d_m/2).

If d_2, …, d_m are all even, the wave reaches the left end. Write d_1 = 2^s·u with u odd: u ≥ 5 adds s + 1 blocks on
the left (P' = ((u−1)/2, (u+5)/2, u, 2u, …, 2^(s−1)u, d_2/2, …, d_m/2)); u = 3 is a visit to the left end in state F
(steps 81 and 1,135); **u = 1 is the halt.** On the tape this is: at the left end the wave halves the first block
again and again (c → c/2 − 2, the "first block roughly halves between returns" of the first entry, e.g.
192 → 94 → 45), and when c reaches 0 the next transitions are B0 C0 D1 E0 C0 D0. That is the only way to reach D0:
every other C0 in the model is entered from B0, with B's 1 to its left.

All of this is one number: with **N = 10 + Σ p_l·2^(m−l)** (the blocks read as binary digits, p_m the units), the
wave goes v₂(N) + 1 blocks deep, reaches the left end exactly when 2^(m−1) divides N, and **the machine halts if and
only if N is a power of two at some super step**.

**Why the returns are rare.** The wave is a binary carry: to reach the left end it has to pass all m blocks, which
needs v₂(N) ≥ m − 1. If N's low bits behave like coin flips, that happens about once every 2^(m−1) super steps, and
each return adds at least one block. The observed gaps fit: m = 11 → 14 blocks at the return at macro step 542, the
next return 56,176 macro steps later (2^(m+1) = 32,768 at m = 14); then 42,352 (65,536), 241,552 (524,288),
1,380,464 (2,097,152). Machine steps grow roughly as the square of the macro step count (the tape holds 3k + 6 ones
after k macro steps: every macro step adds exactly three), so the returns thin out fast:

| macro step | machine step | first c at the left end (then halved while even) |
|---:|---:|---|
| 542 | 2,023,931 | 192, 94, 45 |
| 56,718 | 26,618,972,322 | 110,037 |
| 99,070 | 64,022,989,933 | 175,000, 87,498, 43,747 |
| 340,622 | 755,504,733,976 | 214,534, 107,265 |
| 1,721,086 | 20,158,696,255,640 | 1,588,452, …, 198,553 |
| 13,775,502 | 1.08·10¹⁵ | 5,955,848, 2,977,922, 1,488,959 |
| 389,093,150 | 8.6·10¹⁷ | 666,308,297 |
| 539,460,350 | 1.6·10¹⁸ | 666,595,623 |
| 653,532,558 | 3.1·10¹⁸ | 721,789,438, 360,894,717 |
| 3,471,184,510 | 7.9·10¹⁹ | 1,697,194,888, …, 424,298,719 |
| 14,329,196,574 | 1.4·10²¹ | 4,349,076,901 |

(`c/blkrun.c`, the same model in C with 128-bit step counts, checked against `waves.py` in the tests; full list in
`runs/left_arrivals_macro.txt`: 16 arrivals, 33 new left cells, up to 7·10¹⁰ macro steps.) None of
these has c + 4 a power of two, so **no halt in the first 3.7·10²² machine steps (7·10¹⁰ macro steps; computed, resting on the model)**.

**Halting, heuristically.** At a return the value that decides is d_1, a number of the size of the first blocks
(now about 10⁹). If it behaved like a random integer, the chance of a power of two at each return would be about
1/d_1, and the sum over all future returns (sizes growing geometrically) is far below 10⁻⁶. So the machine almost
certainly runs forever, but a proof has to show that N never lands on a power of two: a Collatz-like question about
one orbit. There is no easy modular obstruction: in the first 200,000 super steps N takes every residue modulo each
q from 3 to 21 (**heuristic**: looked at, not a theorem about all super steps).

**How this relates to the proved macro step.** The entry above proves, in Lean, a macro map in a different cut
(`X(ls, n, cs)`, A at the start of the head's block) and that the machine halts iff that map's run reaches
"n odd, every left block 2". In that cut my wave is
a sequence of its macro steps (its n is my c − 1): my cycles are its transfers, my "c even, move on" is its carry
(n odd), a level with y = 2 being a block of 2 that the carry eats, my odd end is its sweep (n even), and the halt at
the left end is its carry eating blocks of 2 up to the left end. Both models describe the same run, and
`tests/test_waves.py` checks that they agree: from each of the first 2,000 configurations of `py/macro.py`, direct
simulation reaches the next event of `waves.py` at the step and with the block list `waves.py` gives. So "N is a power
of two" is a restatement of the proved halting condition along the orbit; what is not in Lean is the super step itself.

**What a Lean proof would need.** (1) The super step (`superstep`) as a theorem about `next` from `lean/Macro.lean`:
four of my macro steps are a bounded number of `next` steps plus the wave's levels, so this is bookkeeping;
(2) a proof that the orbit of P never makes N a power of two. (1) is routine; (2) is the open problem.

## October 29, 2026: looking for an invariant that keeps N off the powers of two

**Result: none found, and the evidence says there is no simple one.** The question was whether the orbit of the
super step keeps some property that every power of two lacks, so that "N is never a power of two" would follow by
induction. Four families were tried (`py/n_search.py`; everything below rests on `waves.superstep`, which is computed
and tested, not proved in Lean). Nothing new is proved in Lean in this entry.

**Residues of N** (**computed**, `python3 py/n_search.py residues 4000000`, super steps 1,000 to 4·10⁶). For every
odd q from 3 to 127, N takes every residue mod q that a power of two takes. That rules out any invariant "N mod q
avoids a set S" with S containing the powers of two's residues. The stronger version ties the residue to N's size: a
power of two with a + 1 bits is 2^a, so an invariant could say "while N has a + 1 bits, N mod q ≠ 2^a mod q". For each
odd q ≤ 127 and each class c mod ord_q(2) that the run visits often enough (at least 20q super steps with N's bit
length ≡ c + 1), the pair (c, 2^c mod q) occurs. The classes left out are thin only because N's bit length takes few
values (23 to 48) in this range; none of them is a miss among well-sampled classes. Mod powers of two there is
nothing to find: the left-end visits themselves have v₂(N) ≥ m − 1.

**Binary digits** (**computed**, `py/n_search.py digits 4000000`). A power of two has one 1 bit. N's popcount at each
bit length has the minimum a random number would give in that many samples (for example 10 at 48 bits over 556,125
super steps, where a uniform 48-bit number gives popcount ≤ 10 about 7 times). Its leading bits come within
15 zeros of a power of two (super step 166,051: N = 0b1000000000000000011…, 38 bits), so there is no gap below or above
the powers of two in the top bits either.

**The right end is a fixed gadget** (**proved by hand** from the super-step formula, and seen in the run). With
d_{m+1} = 20 the last block cycles 11 → 13 → 14 → 12 → 11: 11 and 13 give d_m = 21, 23, odd, so the wave turns at
once and the block becomes (d_m + 5)/2 = 13, 14; 14 and 12 give d_m = 24, 22, even, and the block becomes d_m/2 = 12,
11, whichever way the wave ends. So N is odd, odd, even, even in turn (the depth sequence reads 0 0 x y), and the
block before it is 19 or 21 at the start of each cycle. Further left the blocks are no longer finite-state (8, 29, 43,
98 values at depths 2 to 5 from the right) and lie between about 3·2^j and 48·2^j at depth j. This is an exact pattern the
map keeps, but it is about N's last bits, which say nothing about N being a power of two: the left-end visits make
N divisible by 2^(m−1) anyway.

**Growth bounds on the blocks cannot do it on their own.** Halting depends only on N, and N is a sum: any lower
bound on the blocks only bounds N from below, and there are block lists with arbitrarily large blocks and N a power
of two. At a visit the deciding number is d_1 = N/2^(m−1) = p_1 + d_2/2, set mostly by the first blocks, which are
fossils of the previous visit (P' = ((u−1)/2, (u+5)/2, u, 2u, …)) changed only by rare deep turns. A bound of the form
"d_1/2^m stays in a window with no power of two" would settle it, but the run's values of d_1/2^m at its visits
(2.25, 1.5, 0.28, 0.23, 0.096, 6.7, 5.3, 0.82, 1.51, 0.355, …) wander over two decades.

**The map itself halts at the random rate** (**computed**, `py/n_search.py starts 60 20000`). From the 3,600 starts
[a, b] with 1 ≤ a, b ≤ 60, the super step reaches the left end 20,910 times in 20,000 super steps each and halts
217 times. If d_1 were a random integer at each visit, the expected count would be Σ 1/(d_1 ln 2) ≈ 239. So the
super step has no invariant of its own shape that forbids halting: started near the blank-tape orbit it halts as
often as chance says. Any proof that the blank-tape run never halts has to use something special about that one
orbit.

**What the evidence says.** By every test the deciding number d_1 behaves like a random integer that grows
geometrically from visit to visit (10⁹ now); the chance that it is ever a power of two from here on is far below
10⁻⁶ (the estimate of the previous entry stands). That is heuristic. A proof would need an argument of the kind
nobody has for Collatz-like orbits; none of the four families above can give it. Lean has nothing new to prove from
this search.

## October 29, 2026: the super step and the power-of-two criterion, proved

**Proved in Lean, kernel only** (`lean/Wave.lean`, standard axioms): (1) of the wave entry above ("What a Lean proof would need") is done, and the whole
halting criterion with it. `halts_iff_pow2'`: the machine halts from blank tape iff some P of the super orbit from
(1, 6) has N = 10 + Σ p_l·2^(m−l) a power of two, with `superstep` the formula of `waves.py`.

How it goes, in the cut of `Macro.lean` (lists nearest first, L = [p_m, …, p_1]):

- The tape [P, 5, 0] is `X (5 :: L) 0 []`, reached at macro step 5 (step 136). Five `next` steps lead to the first
  carry of the wave, `carry ((p_m + 8) :: …)`: the carry value is always d − 2, where d is the wave's value at that block.
- `carry_wave`, by induction on L (and `carry_left`, by induction on fuel, for the halvings at the left end): a carry
  with value d − 2 does one of four things. d = 3: it meets a block of 1 and A sweeps right. d = 4: it eats a block of 2
  inside the same `next` and goes on with p + 2. d odd ≥ 5: a transfer phase, then a sweep (the turn). d even ≥ 6: a
  transfer phase, then the carry again with p + d/2. Throughout, the blocks on the right are `c0 :: R ++ [1]`, and the
  sweep at the end turns them into exactly the blocks d/2 the wave has left behind (`pre`, `sweep_pre`).
- `wave_none_iff`: the wave halts iff d + 2·S(L) is a power of two, with S the blocks read as binary digits; for the
  first block d = p_m + 10, which is N.
- `run_halts_iff`: since the macro run is deterministic (`Res.run_det`) and each super step takes at least one macro
  step, the run from `X (5 :: L) 0 []` halts iff the super orbit hits a power of two. With `halts_iff` this is the
  theorem. `orbit_tape` adds that every tape of the orbit occurs on the machine's run from blank tape.

The proofs follow the macro run without step counts (`Res`), so the step counts of `waves.py` and its finer events are
still computed, not proved. `superstep` is checked by `decide` against the examples in `waves.py`.

**Open, now exactly**: whether N is ever a power of two along the orbit from (1, 6).

## October 30, 2026: the step count of the super step, proved, and the orbit checked to 10²⁴ steps

**Proved in Lean, kernel only** (`lean/WaveTime.lean`, standard axioms): `super_steps`. From the tape [P, 5, 0] the
machine reaches [P', 5, 0] in exactly `superT` steps, or, if the super step halts, makes exactly that many steps and
then the halting transition. In the cut of `Macro.lean` (L = [p_m, …, p_1]):

    superT = 200 + Σ_{blocks passed, d = 2q even} (2q² + q − 5) + (2q² + 4q + 17 + A)   at the turn, d = 2q + 1,

with A = 3 + Σ (q + 1) over the blocks passed (the sweep back over the blocks the wave left on the right). At the left
end the wave goes on with p = 0, and the halt (d = 4 there, the last block of 2) costs 11. The first 200 steps are five
macro steps (164) and the transfers before the first carry (36). The proof follows `carry_wave` again, now with
`runFrom` and its times (`Reach`, `carry_wave_t`, `carry_left_t`); the only new fact is the sweep's time
(`sweep_pre_t`: m + 6 + c0 + 3e + Σ (r + 2)). The formula equals the sum of `waves.py`'s four macro steps on 300,000
super steps, and the search thread's independent closed form (210 + Σ g(d) …) on the same steps (**computed**).

`orbitT` runs the super orbit with the time, tail recursive. `orbitT_steps`: if the machine is at [L, 5, 0] after t
steps, it is at the end of `orbitT j L t` after the step it gives. `runs_of_orbitT` makes that a no-halt bound from the
tape [1, 6, 5, 0] at step 136 (`orbit_start`).

**The orbit, checked in chunks.** `lean/orbit_gen.py` cuts the orbit at checkpoints computed by `c/orbitck.c` (the same
super step and step count in C, about 50 million super steps a second) and writes one theorem per chunk,
`orbitT n P T = some (P', T')`, so Lean recomputes everything and the checkpoints are not trusted. Each file chains
its chunks with `orbitT_trans`, so `lean/check_orbit.sh` checks the files in parallel.

- **Lean, kernel only**: `blank_runs_1_4e16`, no halt in the first 1.4·10¹⁶ steps: 10⁷ super steps in 1,000 chunks of
  10⁴, `decide +kernel`, 3,030 s on three cores. The kernel needs about 1 ms per super step; chunks much longer than
  2·10⁴ slow down sharply (10⁵ did not finish in 10 minutes), hence the many short ones.
- **Lean, `native_decide`**: `blank_runs_1e24`, no halt in the first 10²⁴ steps: 9.9·10¹⁰ super steps, the kernel's
  10⁷ then 99 chunks of up to 10⁹, ending at step 1,020,655,748,109,356,278,914,592. `check_orbit.sh` compiles the
  modules the chunks call to C with the same `lean -c` and links them with `leanc` (what Lake's `precompileModules`
  does), and loads the library with `--load-dynlib`: about 250 ns per super step against several µs interpreted;
  the 99 chunks take about 6 CPU hours (`set_option maxHeartbeats 0`: compiled evaluation counts against the limit). This
  covers the C run of the wave model to 3.7·10²² steps, whose step count was the unproved part.

The search thread built a faster route on top of `WaveTime.lean` (tabulating the periodic bottom blocks, PR #124: no
halt in 4.4·10³⁷ steps with `native_decide`); the direct check here is the simple independent one, resting only on
`orbitT`.
