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

## October 30, 2026: the right end is periodic, and no halt in the first 2.7·10⁴⁹ steps

**Result** (**computed**, `c/superrun.c`, resting on the proved criterion): the super orbit from (1, 6) runs
599,258,349,609,526,266,612,571 (6.0·10²³) super steps without N becoming a power of two, so **the machine does not halt in its first 2.7·10⁴⁹ steps**
(27,264,770,338,578,141,293,580,742,812,737,757,101,373,338,361,002 exactly). The previous bound was 3.7·10²² (7·10¹⁰ macro steps, 1.75·10¹⁰ super steps). The run took 40 minutes on
one core and 8 GB, and stopped there when it ran out of memory (a Lean build started beside it); the last exact
point it printed is the bound. The method below is what made the difference, not the hardware.

**The levels only talk upward.** Number the blocks from the right end: level 0 is p_m, level 1 is p_{m−1}, and so on.
Read from the right, `superstep` is a cascade. Every super step level 0 receives a wave with h = 10. A level with block
p that receives a wave h computes d = p + h; if d is odd the block becomes (d + 5)/2 and the level above receives an
*add* of (d − 1)/2 (its block grows by that and the super step ends); if d is even the block becomes d/2 and the level
above receives a wave with h = d/2. The top level always passes the wave on to the left end, where the left-end rule
of `superstep` replaces it by new levels. (This is the formula of `superstep` with d_{l} = p_l + d_{l+1}/2; the turn
is at the first odd d from the right.) Nothing ever flows down: **the bottom k levels are an autonomous system**, the
same whatever happens above them, and the left end only ever touches the top.

**The bottom levels become periodic** (**computed**, exact). A wave halves a level's block, so a level driven by a
periodic input forgets its start and falls into a cycle. Level 0 is the known cycle 11 → 13 → 14 → 12 (period 4).
Levels 0 and 1 together have period 8, levels 0 to 2 period 32, and so on: the bottom k levels repeat with period
Q_k = 2^a·5^b super steps, where each level multiplies the period by L ∈ {1, 2, 4, 5}. In the run:

| levels | period (super steps) | events per period into the next level |
|---:|---:|---:|
| 1 | 4 | 4 |
| 10 | 65,536 | 156 |
| 20 | 1.7·10¹⁰ | 40,412 |
| 30 | 1.7·10¹⁴ | 409,010 |
| 40 | 1.1·10¹⁹ | 26,141,759 |
| 44 | 1.8·10²¹ (5⁵·2⁵⁹) | 261,414,036 |

(The full list is in `runs/superrun_long.txt`, lines `table`.) So the earlier note that the blocks "further left are
no longer finite-state" was only true of short windows: each level is finite-state once the levels below it have
settled, with a period that grows about fourfold per level.

**The search.** `c/superrun.c` keeps, for the bottom K levels, one period of what they send to level K: a table of
(super steps since the last event, add or wave, its value, the machine steps spent below level K). It runs levels
K, K + 1, … explicitly from the table. Whenever level K's block is the same at two passes through the table, L passes
later it is periodic for good (its input is periodic and its state recurred); the program then checks that L passes
bring it back, builds the table for K + 1 from those L passes, and drops level K from the explicit part. Each level
halves the work per super step and roughly doubles the table, so memory sets the limit: 44 levels, 2.6·10⁸ entries of
32 bytes. A pass through that table is 1.8·10²¹ super steps and takes about 7 seconds. Multiple threads would only
split that sweep (at most the core count, about 4×, against the factor 2 per level from the tables), so the other
cores ran the independent checks below instead.

**Machine steps per super step** (**computed**, exact): from [P, 5, 0] to the next [P′, 5, 0] the machine takes
210 + Σ g(d) over the levels that receive a wave, + 17 for the level that receives the add, with
g(d) = (d + 1) + cyc(d − 4) + 3 + ⌊(d − 4)/2⌋ and cyc(c) = j(2c + 7) − 2j², j = ⌊c/2⌋. At the left end the wave goes
on through virtual levels with p = 0 (d → d/2): each costs g, an odd end 17, and d = 3 (the visit in state F) 16. This
is a per-level split of the step counts of four `waves.step`s; the parallel Lean thread proves the same count
(`super_steps`, `lean/WaveTime.lean`) in another closed form and checked that the two agree.

**Checks** (`tests/test_superrun.py`, about 20 s, and runs made for this entry):

- the tape and machine step after each of the first 4,000 super steps (direct mode) equal every fourth event of
  `waves.step`;
- the tabulated run and the direct run (no tables) agree on every return to the left end (super step, machine step,
  d₁, number of blocks) to 3·10⁸ super steps in the test, and to 2·10¹⁰ super steps in a separate run (16 returns,
  9 minutes);
- the returns up to 1.75·10¹⁰ super steps are exactly the 15 of `runs/left_arrivals_macro.txt` (`c/blkrun.c`), at
  macro step 4S + 2 with c = d₁ − 4; and `blkrun` run to macro step 4S + 3 ends at the same machine step as the
  tabulated run, for S = 867,796,127 (`SUPERRUN_LONG=1`) and S = 3,582,299,143 (step 1,418,025,594,627,195,513,086);
- `py/superrun.py`, the same method written again in Python with big integers, agrees on every return to 10¹⁴ super
  steps in the test (and to 2.2·10¹⁶, 28 returns, in a separate run);
- from 144 other starts [a, b] (a, b ≤ 12), direct and tabulated runs return to the left end and halt where
  `waves.superstep` says.

**The returns to the left end** (`runs/superrun_long.txt`): 38 in all, 23 of them beyond the old bound. N is a power of two
only at a return (N = 2^a > p₁·2^(m−1) forces 2^(m−1) | N), and there N = 2^(m−1)·d₁, so the question at each return
is whether d₁ is a power of two.

| super step | ends at machine step | blocks m | d₁ | s (d₁ = 2^s·u) | distance to a power of two |
|---:|---:|---:|---:|---:|---:|
| 1.8·10¹⁰ | 5.4·10²² | 36 | 136,109,454,645 | 0 | 2^−6.7 |
| 6.9·10¹⁰ | 4.8·10²³ | 39 | 362,386,972,244 | 2 | 2^−2.0 |
| 7.1·10¹⁰ | 6.7·10²³ | 40 | 133,415,690,549 | 0 | 2^−5.0 |
| 5.1·10¹¹ | 3.3·10²⁵ | 42 | 1,833,747,547,526 | 1 | 2^−2.3 |
| 1.2·10¹² | 1.6·10²⁶ | 45 | 4,249,040,973,972 | 2 | 2^−4.8 |
| 6.1·10¹² | 4.1·10²⁷ | 47 | 10,664,595,800,010 | 1 | 2^−2.5 |
| 3.0·10¹³ | 9.8·10²⁸ | 49 | 54,199,241,040,550 | 1 | 2^−1.7 |
| 7.7·10¹³ | 5.7·10²⁹ | 50 | 105,513,857,879,651 | 0 | 2^−1.6 |
| 4.6·10¹⁴ | 3.4·10³¹ | 52 | 1,771,795,407,360,090 | 1 | 2^−1.9 |
| 3.2·10¹⁵ | 1.3·10³³ | 53 | 21,867,971,409,200,949 | 0 | 2^−2.5 |
| 7.3·10¹⁵ | 6.0·10³³ | 54 | 45,318,386,059,614,339 | 0 | 2^−2.3 |
| 7.9·10¹⁵ | 9.6·10³³ | 55 | 47,464,895,168,271,501 | 0 | 2^−2.0 |
| 2.2·10¹⁶ | 6.5·10³⁴ | 58 | 89,820,924,989,445,148 | 2 | 2^−2.3 |
| 4.2·10¹⁷ | 2.2·10³⁷ | 66 | 3,313,553,021,126,728,576 | 7 | 2^−1.7 |
| 7.2·10¹⁸ | 5.9·10³⁹ | 68 | 11,010,273,142,654,137,366 | 1 | 2^−2.6 |
| 1.1·10¹⁹ | 1.2·10⁴⁰ | 69 | 11,975,792,871,741,497,919 | 0 | 2^−2.1 |
| 2.2·10²⁰ | 4.7·10⁴² | 71 | 300,313,912,483,936,881,826 | 1 | 2^−5.9 |
| 1.4·10²¹ | 2.2·10⁴⁴ | 72 | 4,887,045,305,511,716,897,389 | 0 | 2^−4.9 |
| 1.4·10²¹ | 3.1·10⁴⁴ | 73 | 5,573,632,706,148,772,833,103 | 0 | 2^−2.7 |
| 2.4·10²¹ | 6.8·10⁴⁴ | 75 | 7,368,707,619,864,359,689,538 | 1 | 2^−1.8 |
| 7.0·10²¹ | 4.6·10⁴⁵ | 77 | 9,492,689,577,801,098,865,030 | 1 | 2^−7.6 |
| 2.7·10²² | 8.9·10⁴⁶ | 78 | 104,112,580,301,255,728,770,643 | 0 | 2^−1.9 |
| 3.1·10²³ | 1.2·10⁴⁹ | 81 | 1,874,777,618,886,538,568,719,180 | 2 | 2^−1.8 |

**How close N came to a power of two.** Measured as the relative distance of d₁ (equivalently of N) to the nearest
power of two, the closest return is the one at super step 7.0·10²¹ (m = 77): d₁ = 9,492,689,577,801,098,865,030 lies 2^−7.6 (0.5 %) above 2⁷³, so N = 2⁷⁶·d₁, just above 2¹⁴⁹, misses it by about 4·10⁴². Over 38 returns a uniformly random mantissa would give a closest
approach of about 2^−(log₂ 38 + 1); the run is in line with that. In absolute terms the misses are enormous: d₁ is
now about 1.9·10²⁴ (81 bits), so N = 2⁸⁰·d₁ is about 2^160.6 and the nearest power of two is more than 10^47 away.
(Corrected on 30 October 2026, see the last entry: this line first said 1.9·10²⁷, 91 bits, 2^171 and 10^49.)

**What this rests on.** That the orbit decides halting is proved (`halts_iff_pow2'`). That the run follows the orbit
rests on `c/superrun.c` (trusted C, tested as above, with the periodicity of each tabulated level checked by the
program before it is used). The step count rests on the per-level formula (computed and tested; the Lean
step-count proof is in progress separately). This is a computation, not a proof of anything beyond the bound.

**Can the cycles be proved?** For each fixed k, yes by computation: autonomy is a short lemma about `superstep`, and
a cycle is a state that comes back, which the tables certify level by level (the program checks exactly this before
it uses a table). That is the route for carrying the tables into Lean, next. For every k at once there is a hand
argument of the form "periodic or no halt": if the bottom k levels are periodic and send level k at least one wave
per period, level k stays bounded (each wave halves it, the adds per period are bounded) and so cycles; if they
eventually send none, the wave never passes level k again, never reaches the left end, and the machine never halts.
Neither says anything about whether some d₁ at a return is a power of two.

## October 30, 2026: the tables in Lean, and no halt in the first 4.4·10³⁷ steps (native_decide)

**Proved in Lean, kernel only** (`lean/Cascade.lean`, on top of `WaveTime.lean`'s `superT` and `orbitT`):

- `superL_split`, `superT_split`: with the list nearest first split as B ++ U (U not empty), the super step of B ++ U is
  B's own step (`bstep`, what the cascade of the entry above does to B) followed by what B passes on (`Ev`: nothing, an
  add, or a wave) applied to U; and `superT` splits the same way, each level accounting for its share of the steps
  (`lev`: `oddT d 0` where the wave turns, `evenT d + d/2 + 1` where it passes). So **the last k blocks run on their
  own**, for every k and every list.
- A table is a list of entries (super steps, event, steps of the bottom) with a tail; `Rep B T tl` says it is one
  period of the bottom B (the chain of quiet stretches and events comes back to B). `pass_sound`, `passes_sound`:
  running only U on the table follows `orbitT` of B ++ U over whole periods, steps included.
- `build_rep`: if the first level of U, with block p, comes back to p after L passes of a period of B, the table that
  `build` computes is a period of B ++ [p]. Nothing about periodicity is assumed: `build` returns the level's block at
  the end, and `drive` refuses to go on unless it is p again.
- `drive_sound`, `runs_of_drive`: a plan (passes, then a level to add, …) that `drive` runs from [6, 1] at step 136
  to machine step t gives `∃ c, steps t init = some c`.

**Proved with `native_decide`** (`lean/CascadeRun.lean`, about 4 minutes): `blank_runs_4e37`, **no halt in the first
44,405,698,359,075,157,430,295,693,458,238,990,120 steps** (6.75·10¹⁷ super steps; past the return to the left end
at super step 4.2·10¹⁷). The plan is `python3 py/superrun.py plan 35 6`: tables for the last 1 to 35 blocks, then 6
passes of the last table (8.8·10¹⁶ super steps each). The plan is only a hint: every table it asks for is computed and
checked inside the evaluation. 30 levels give 1.2·10³² steps in 38 seconds; each further level roughly doubles the
time and the reach. (The C run's 2.7·10⁴⁹ used 44 levels and 8 GB, beyond what Lean's lists hold comfortably.)

Before this the Lean bounds were 2·10¹⁰ (kernel) and 9·10¹³ (`native_decide`); the step-count thread's chunked
`orbitT` check, which uses none of the cascade, goes to about 10²⁴.

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
  the 99 chunks take about 4 CPU hours (`set_option maxHeartbeats 0`: compiled evaluation counts against the limit). This
  covers the C run of the wave model to 3.7·10²² steps, whose step count was the unproved part.

The search thread built a faster route on top of `WaveTime.lean` (tabulating the periodic bottom blocks, PR #124: no
halt in 4.4·10³⁷ steps with `native_decide`); the direct check here is the simple independent one, resting only on
`orbitT`.

## October 30, 2026: each level cycles, or the machine never halts (Lean)

**Result** (**proved**, `lean/Cycles.lean`, kernel only, 3 s): for every k and every state B of the last k blocks
(nearest first), there is an n after which the bottom on its own (`bs`, the iterated `bstep` of `Cascade.lean`)
either **cycles**, coming back after some m > 0 super steps, or is **silent**, never passing an add or a wave to the
left again (`cycles_or_silent`). A cycling bottom has a table of one period (`rep_of_cycles`). A silent bottom on the
orbit from blank tape, with blocks to its left, means the machine never halts (`never_halts_of_silent`): the wave
never reaches the left end again. On the orbit (`cycles_or_never_halts`): once the orbit has the last k blocks B at
super step j, either the machine halts within n more super steps, or at super step j + n the bottom is `bs n B` and
cycles, or the machine never halts.

This corrects the hand version in the first entry of today, "periodic or the wave stops reaching the left end". The
bottom can also halt the machine before it settles, so the correct statement has three cases. It decides nothing by itself, since
any of the three could hold for the real orbit.

**The proof**, by induction on k. If the bottom is silent, one more level only ever receives nothing, so it is silent
too. If the bottom cycles with period m and passes on at least one wave per period, the next level's block goes from
q to F(q) per period with 2·F(q) ≤ q + 2W, where W bounds what one period adds (a wave h turns q into at most
(q + h + 5)/2). So the block stays at most q₀ + 2W, takes at most q₀ + 2W + 1 values, and repeats by pigeonhole: the
bottom with one more level cycles with period a multiple of m. If the bottom passes no wave in a period, it never does,
and the next level only receives adds, which it keeps: silent. Everything is in core Lean (own pigeonhole and
iteration); `#print axioms` shows propext, Quot.sound and Classical.choice (from `by_cases`).

**The first six levels, checked** (`cycle₁`–`cycle₆`, `decide`, no axioms): the orbit from blank tape at super step
3, 7, 11, 31, 60, 163 has last blocks [12], [12, 26], [12, 27, 39], [12, 26, 27, 38], [11, 19, 28, 47, 111],
[12, 27, 36, 37, 93, 184], and these come back after 4, 8, 32, 128, 256, 1024 super steps but not after half of that.
Since each period is a power of two, it is the least one. So the last six blocks cycle for as long as the machine
runs. Each further level is still computed only (`c/superrun.c`, up to 44 levels).

## October 30, 2026: why the period factors are 1, 2, 4 or 5

**The question.** Each level added to the bottom multiplies the period by L ∈ {1, 2, 4, 5} (44 levels in
`runs/superrun_long.txt`; Q₄₄ = 5⁵·2⁵⁹). Is there a rule?

**The rule: mod 5, a wave is affine.** A level with block p that receives a wave h becomes (d + 5)/2 if d = p + h is
odd and d/2 if it is even. Both are 3d mod 5 (2·3 = 6 ≡ 1, and the +5 vanishes), so mod 5 a wave is p ↦ 3(p + h)
whichever way it goes, and an add v is p ↦ p + v. Over one period of the bottom, the level's block therefore moves mod
5 by an affine map r ↦ a·r + b with **a = 3^W mod 5**, W the number of waves the level receives per period, and b the
image of 0. The level's own period L is the orbit length of its residue under that map, and the orbits of an affine map
of ℤ/5 have length 1, 2, 4 or 5, never 3:

| W mod 4 | a = 3^W | possible L | which |
|---:|---:|---|---|
| 1 or 3 | 3 or 2 | 1 or 4 | 1 iff the residue is the map's fixed point |
| 2 | 4 | 1 or 2 | 1 iff the residue is the fixed point |
| 0 | 1 | 1 or 5 | 5 iff b ≠ 0 (then every residue cycles), 1 iff b = 0 |

The 5 in L = 5 is the translation part of the map and the 4 is the order of 3 mod 5; that is why the periods are
2^a·5^b.

**Proved in Lean, kernel only** (`lean/Periods.lean`, 4 s, on top of `Cycles.lean`'s pass map `topv m C`, the next
level's block over m super steps of the bottom C):

- `topv_mod`, `topm_aff`: mod 5 the pass map is `r ↦ 3^W r + b`, W = `wc m C` the waves the bottom passes on, b =
  `topm m C 0`.
- `cycle_residues`: if the bottom passes on at least one wave per period, two blocks of one cycle of the pass map are
  never congruent mod 5. Two blocks 5c apart stay 5c′ apart with c′ ≤ c, and c′ < c after a wave if c ≥ 2
  (`lev_shift`, `topv_shift`). Around a cycle c cannot shrink, so c = 1 for ever; then F^j moves the cycle up by 5 each
  time, which a cycle cannot do (`no_shift_cycle`).
- `period_factor`: so if the block has least period L under the pass map, L is the least period of its residue under
  the affine map: L ∈ {1, 2, 4, 5}, with the table above, and L = 1 exactly when the residue is fixed. `level_period`:
  the bottom with that level comes back after L·m super steps.
- `rule₁`–`rule₃`: the rule on the orbit's first three levels (W = 1, 2, 3; L = 4, 2, 4).

A shorter hand proof of `cycle_residues`, not in Lean: a wave maps any 5 consecutive blocks one-to-one onto 5
consecutive blocks (2q … 2q + 4 ↦ q, q + 3, q + 1, q + 4, q + 2, and 2q + 1 … 2q + 5 ↦ q + 1 … q + 5), with the lowest
going to ⌈(c + h)/2⌉. So the pass map F sends each window [c, c + 4] onto a window [G(c), G(c) + 4], G is monotone
and halves, so its iterates settle on a fixed point c*, and every orbit of F ends in an invariant window [c*, c* + 4],
which F permutes as the affine map permutes ℤ/5.

**Computed** (`c/superrun.c -r`, `runs/periods_rules.txt`, all 44 levels of the long run; `tests/test_superrun.py`
repeats levels 0 to 25):

- every factor L equals the orbit length the rule predicts, and every cycle spans at most 5 consecutive blocks;
- from level 3 on (W ≥ 7) the pass map near the cycle depends only on the block mod 5 and permutes 5 consecutive
  blocks: **a settled level remembers only its residue mod 5** from one period to the next. The whole state of the
  settled bottom is one residue per level (plus the phase within the period).
- the factors: L = 4 at 26 levels, 2 at 7, 1 at 6, 5 at 5. W mod 4 is 3 at 19 levels, 1 at 10, 2 at 9, 0 at 6.
  With W mod 4 and the residue uniform, the rule gives L = 4, 2, 5, 1 with probability 2/5, 1/5, 1/5, 1/5 and
  1.46 bits of period per level; the run has 1.60 (70.6 bits over 44 levels).

**Deep waves are 28 % more frequent than coin flips** (**computed**). Level k receives W_k waves per period Q_k, so on
average a wave reaches level k at the rate W_k/Q_k per super step, and 2^k·W_k/Q_k is the factor by which
"2^k divides N" is more frequent than for a random N. It is 1, 1, 1.5, 1.75 for k = 0 to 3, and then settles:

| k | 10 | 20 | 30 | 35 | 40 | 43 |
|---:|---:|---:|---:|---:|---:|---:|
| 2^k W_k/Q_k | 1.2500 | 1.2718 | 1.2777 | 1.2765 | 1.2765 | 1.2764 |

It converges, presumably because a level with W waves per period passes on half of them up to about W^(−1/2)
(a heuristic), and W_k grows twofold per level. So the time-average chance that the wave passes the last k blocks is 1.2764·2^−k: the low bits of N
are biased towards 0, by a constant factor and not more.

**What this means for N and halting.** The rule settles the structure of the bottom completely: it is a deterministic
system in which each settled level carries a residue mod 5, and its period, its pattern of waves, and N mod 2^k for
k up to the settled depth follow from those residues. It says nothing about the top levels, where the returns to the
left end happen and halting is decided (d₁ at a return, now 1.9·10²⁴, a power of two or not), and the residue each
level settles on is set by the top when that level is young. So the rule gives no obstruction to a power of two, and
the heuristic is unchanged in kind (**heuristic**): d₁ is now 1.9·10²⁴ (81 bits), it has grown by about 2.1 bits per
return (log₂ d₁ from 3.2 to 80.6 over 38 returns), and Σ 1/(d₁ ln 2) over the future returns is about 5·10⁻²⁵ (corrected
on 30 October 2026: this first said 1.9·10²⁷, 91 bits, 2.4 bits and 10⁻²⁷, from a misread d₁; see the last entry). The one sharpening
is the factor ρ = 1.2764 for the wave depth: the gaps between returns are shorter than 2^(m−1) super steps (the
measured gaps over 2^(m−1)/ρ have median 0.43; the top levels, fresh from the left end, are not coin flips either),
which changes how many returns come per machine step, not the chance per return.

## October 30, 2026: the cycles of the last 30 blocks, and no halt in the first 1.2·10³² steps, by the kernel alone

**The last 1 to 30 blocks cycle on the orbit, with their least periods** (**proved, kernel only**: `cycle1`–`cycle30`,
`lean/CycleRun.lean`), and **no halt in the first 120,264,458,847,608,883,162,407,865,309,662 steps** (1.2·10³², the
same: `blank_runs_cycles`), up from 1.4·10¹⁶ by the plain orbit. The periods are 4, 8, 32, …, 171,798,691,840,000
(1.7·10¹⁴ super steps for the last 30), the factors from level 7 on ×4, ×1, ×4, ×4, ×5, ×1, ×4, ×4, ×2, ×5, ×4, ×5,
×4, ×4, ×4, ×4, ×5, ×1, ×1, ×4, ×4, ×4, ×2, ×1, as `c/superrun.c` has them. The bound is the plan of
`lean/CascadeRun.lean` for 30 levels and then 4 passes of the last table: 1.4·10¹⁵ super steps.

**Why pieces.** `drive` (`lean/Cascade.lean`) evaluated by `decide +kernel` checks 16 levels in 14 s and 18 in 56 s,
but its memory doubles with each level (1.8 GB at 16, 5.5 GB at 18) and 20 levels run out of 16 GB: the kernel keeps
every intermediate term of a declaration, about 60 KB per table entry processed. So the work is cut into
declarations. `lean/cycle_gen.py` runs the plan in Python, mirroring the Lean definitions, and writes out every table
(`CycleData/`, read by the `tbl%` term of `lean/TableLit.lean`, which builds the list term directly; the elaborator
takes 30 s and times out on a 20,000-entry list literal, `tbl%` 2 s). Each piece (`CyclePieces/`) is one pass of one
level over a stretch of 3,000 entries of the table below (`lvSeg`), or of the levels further left (`pseg`), from a
written state to a written state, checked by `decide +kernel` in about 3 s. `CycleLevels/` chains the pieces into
`passes` and `build` of `lean/Cascade.lean` (`lvPass_seg`, `lvSeg_app`, `build_segs`, `pass_pseg`), and
`CycleRun.lean` chains the levels from blank tape by `step_sound` (`passes_sound` and `build_rep`). Nothing written is
trusted: a wrong entry fails its piece.

Two traps on the way, both from Lean treating `lenT T + c` as something to compute: any unification or kernel
definitional check of a sum with `lenT T` on a written table that is not syntactically closed evaluates `lenT` on the
whole table (the elaborator hits its recursion limit, the kernel takes minutes, doubling per level). The generated
proofs therefore only ever compare such terms syntactically (`build_len'`).

**Least periods.** For each level the pieces say where the new block is at the end of each of the L passes; each pass
is the pass map `topv m B` (`topv_of_seg`), the block meets its start only after the last, so the least period of the
bottom with one more block is L times the least period below (`least_append`, with `LeastP`: comes back after m, and
only after multiples of m).

**Cost.** 5,920 pieces in 501 files, plus 144 MB of written tables; about 4 CPU hours, an hour on 4 cores
(`check_cycles.sh 30 4`). Each level costs about as much as the size of the table below times the passes over it, so
the cost about doubles per level; 35 levels, the native bound's, would be some 20 times more. CI checks the first 16
levels and 2 passes (`check_cycles.sh 16 2`, about a minute).

## October 30, 2026: the single events in Lean, and DeepMind's high-level map

**Lean, kernel only** (`lean/Events.lean`, `lean/DeepMind.lean`, in `check.sh`):

- `ev`: the event map in closed form. An event is A on the blank right of the last block; with the blocks nearest
  first, `ev (x :: k :: ls)` with q = x/2 is `(q + 2) :: (k + q + 1) :: ls` for even x, and `q :: W` with
  `wave (k + q + 2) ls = some W` for odd x (`none` is a halt). `wave` is the one of `Wave.lean`: the single event uses
  the same wave as the super step, started at another value. Agrees with `waves.py` `step` on the first 200,000 events
  (a one-off Python comparison) and on the examples in the file.
- `carry_ev`: `carry_wave` with any right part. The wave ends with the sweep over `1^e ++ bump cs`, written `close` as
  a list function; `carry_wave` had the right part `c0 :: R ++ [1]` of the super step only.
- `ev_sound`: from `E b` the machine reaches `E b'` when `ev b = some b'` and halts when `ev b = none`, for every b
  with two blocks or more and every block but the last nonempty. `E (x :: ls)` is reached x steps after
  `X ls x []` (A runs over the block); the first macro step from there takes at least x steps (`next_t`), so the run
  from `E b` is the macro run from `X ls x []` minus its first x steps (`steps_sub`).
- `ev4`: four events from `0 :: 5 :: L` are `0 :: 5 :: superL L` (or a halt); `evOrbit_orbit`: 4j events are j super
  steps. `halts_iff_ev`: the machine halts from blank tape iff the event orbit from [2, 1] (step 17) reaches `none`;
  `evOrbit_tape`: every list of that orbit is a tape of the run.
- `lean/DeepMind.lean` copies google-deepmind/cryptids' `bumpHead`, `transferBHL`, `runEpoch` and `highLevelNext`
  (commit `e5f59ed`) into core Lean, with their termination proof. `toHL (x :: ls) = C(x + 1, ls − 1)`, the event two
  steps later. `transferBHL_close`: their sweep onto the left stack is `close`; `runEpoch_wave`: an epoch is the wave;
  `highLevelNext_eq`: `highLevelNext (toHL b) = (ev b).map toHL` for every event of the run. So `halts_iff_hl`: the
  machine halts iff their high-level orbit from C(3, [0]) halts, their `isHalt_iff_highLevel_acceleration` reached
  here through our macro step and super step.

Not proved: the step counts of a single event (`waves.py` has them; `WaveTime.lean` proves only their sum over a super
step), and that no other event lies between `E b` and `E (ev b)`. Lean proves that the run passes through these
events, not that they are all of them; `tests/test_waves.py` checks against direct simulation that they are, for
every event of the first 10⁹ steps.

## October 30, 2026: how the top blocks decide halting, N only grows, and the odds corrected

**A correction first.** The entries above (and the reduction page, `status.json`) put d₁ at the last return at
"1.9·10²⁷ (91 bits)" and the chance of a future halt at about 10⁻²⁷. The value in `runs/superrun_long.txt` is
d₁ = 1,874,777,618,886,538,568,719,180, which is 1.9·10²⁴ (81 bits, log₂ = 80.63); the digits were miscounted, and the
growth was 2.1 bits per return, not 2.4. The lines above are corrected in place, with a note.

**Proved in Lean, kernel only** (`lean/Monotone.lean`, standard axioms, under a second): **N strictly increases at
every super step** (`superL_grows`), so it is strictly increasing along the orbit from blank tape (`orbit_grows`,
`blank_orbit_grows`). Three inductions over `Wave.lean`'s definitions: at the left end the new blocks satisfy
3d < 2·S W (`leftEnd_grows`); through the blocks d + 2·S L < S W (`wave_grows`: a turn gains (d + 3)/2, a passing
level adds d/2 to what the levels above gain). By hand: where the wave turns at block i (j = m − i), N gains
10 − 2^j + (d_i + 5)·2^(j−1) + Σ_{k>i} d_k·2^(m−k−1) > 2^(j+1); at a return,
N' = (3 + s)/2·N + 3·2^(m+s−2) + 10 + ½·Σ_{k≥2} d_k·2^(m−k) (checked numerically on the orbit and 300 random starts).

Consequences: each power of two is met at most once. Between returns m is fixed, so the next d₁ = N_then/2^(m−1) is
larger than N_now/2^(m−1) ≥ p₁ + p₂/2 + p₃/4 + p₄/8. With the top blocks at the end of the long run
(234347202360817321089897, …089900, 2163436398666026041512949, 2273252587298508113309726) that is 1.18·10²⁴ = 2^79.96:
**the next return can halt only if 2⁸⁰ divides d₁** (`py/top_stats.py odds`; the blocks rest on `c/superrun.c`).

**What a return writes** (on paper). With d₁ = 2^s·u the top block becomes (u−1)/2, (u+5)/2, u, 2u, …, 2^(s−1)u. Until
the next return the top block only gains (turns at block 2 add (d₂−1)/2; nothing else reaches it). If all those blocks
survive to the next return, d₁' = ((s+3)u + 3)/4 + h/2^(s+1), h the wave arriving at the block 2^(s−1)u; this holds at
all three returns among the first 31 where they survive (super steps 2, 1.6·10⁸, 7.1·10¹⁰). On the orbit
((s+3)u + 3)/4 has been 0.1 % to 85 % of the next d₁; the rest is carried up from below.

**The odds, redone** (**heuristic**, `py/top_stats.py odds`, `runs/odds.txt`): starting above the floor 2^79.96 and
resampling the 37 observed increments of log₂ d₁ (from the sixth return on), Σ 1/(d₁ ln 2) over the future has median
4.4·10⁻²⁵, mean 6.5·10⁻²⁵, 10 % to 90 % 4.7·10⁻²⁶ to 1.4·10⁻²⁴. Counting time instead (N grows like S^2.06 on this
orbit, density of powers of two 1/(N ln 2)) gives a few times 10⁻²⁵ too. The 2-adic half alone: the next return needs
v₂(d₁) ≥ 80, chance 2⁻⁸⁰ ≈ 8·10⁻²⁵ if the valuation at a return is geometric.

**N mod 2^k at the right end, exactly** (**computed**, `c/bottom2adic.c`, `runs/bottom2adic_18.txt`, 25 s). N mod 2^k
depends only on the last k blocks, which run on their own and cycle, so its time average over one period is exact for
all later times. Over one period of the last 18 blocks (1,048,576,000 super steps from the tape at super step 10⁹; the
blocks come back): v₂(N) = j occurs 1, 0.5, 1.25, 1.75, 2.125, 1.4375, 1.28, 1.375, 1.41, 1.19, 1.23, 1.25, 1.28, … times
2^−(j+1) (the factor 1.2764 of the entry on period factors, level by level); the next bit given the lower ones is off
from 1/2 by 0.10, 0.03, 0.07, 0.04, 0.02, 0.067, 0.032, 0.017, 0.009, 0.036, 0.013, 0.009, 0.013, 0.004, 0.0045, 0.0018
on average at bits 2 to 17, so the 2-adic law of N tends to one with a density, and no class mod 2^k gets more than 3.5
times its share. **N is never 3030 or 4054 mod 2¹²** (binary 1?1111010110); no other residue mod 2¹⁸ is missed. Not
explained; it says nothing about powers of two (0 mod 2¹²).

**At the top of the blank-tape orbit the waves are fair coins** (**computed**, `py/top_stats.py toppass 1e17`,
`runs/toppass_1e17.txt`, 30 s): after super step 10⁶, a wave that reaches the k-th block from the left has d even there
in 0.53, 0.59, 0.53, 0.53 of cases for k = 1 to 4 (19 to 114 waves), and 0.4891 to 0.5067 for k = 5 to 12, 0.4998 to
0.5006 for k = 13 to 24 (over 10⁵ waves each). The valuation s at a return continues those coin flips beyond the left
end; its 38 values (mean 1.0, largest 7) are too few for the tail.

**The random model on the map** (**computed** counts, **heuristic** reading; `c/ensemble.c`,
`py/top_stats.py ensemble`, `runs/ensemble_summary.txt`). 60,000 orbits of 2²⁴ super steps from 2 to 4 random blocks of
1 to 100 (seven runs on four cores, about an hour): 522,749 returns, d₁ up to 2³⁰.
- Halts: 2,018 against Σ 1/(d₁ ln 2) = 2,023.7 (ratio 0.997 ± 0.022); per bit of d₁ the ratio runs 0.56 to 1.52 (low
  for d₁ < 2⁶, high for 2⁷ to 2¹⁰), 8 halts against 4.8 for d₁ in [2¹³, 2¹⁶).
- Near-halts, odd part u < 2^c (expected (2^c/2)/(d₁ ln 2) per return with d₁ ≥ 2^(c+6)), c = 1 to 20: 0.4 to 1.4 of
  expected in every cell with at least 20 expected; pooled, 1.38 (c = 1), 1.20 (c = 2), 0.76 to 1.09 (c = 3 to 20). The
  same count on random numbers of the same sizes gives 0.9 to 1.0 for c ≥ 5.
- v₂(d₁): P(s ≥ t)·2^t within 3 % of 1 for t ≤ 7 in each band; pooled over d₁ ≥ 2¹⁶ it is 0.97, 0.97, 0.89, 0.85, 0.87,
  0.84, 0.69, 0.40 for t = 6 to 13 (−3.2σ at t = 8, −3.0σ at t = 9), not in every band (none in [2²⁰, 2²⁴)), and not in
  random numbers of the same sizes. Orbits do not differ: an orbit with a high valuation early is not more likely to
  have one later (0.95 ± 0.02 against 1.00 ± 0.01 at t = 4), so survivorship does not explain it. Unexplained; it would
  only lower the odds.
- Residues: the residues of powers of two mod odd q ≤ 31 get 0.98 to 1.00 of their share. u mod 2⁸ is not uniform:
  χ² 2.4 to 3.5 times its 127 degrees of freedom even with one return per orbit (so not a correlation artefact), frequencies 0.9 to 1.15, u ≡ 1 mod 2⁸
  at 0.81 to 1.04 of its share by band. Consecutive returns of an orbit agree mod 2^k only at chance (1.00 to 1.03).
- Leading bits: frac(log₂ d₁) uniform within 3 %; 2.00 % of returns within 0.01 of a power of two.

**What it means.** Nothing here comes near a proof. It locates the decision (the top blocks at a return), proves that
N only grows, corrects the odds to about 5·10⁻²⁵, and shows that the random model behind them holds within a factor of
about 2 wherever it can be tested, with the only systematic departure (fewer high valuations) on the side of no halt.
Two partial results look reachable: the right-end law for every k (a 2-adic density for N, which needs control of the
residues the levels settle on), and a deterministic bound on v₂(d₁) at a return from the top blocks. A run of 10⁷
starts (a few CPU days) would settle whether the shortfall in high valuations is real. Page:
`pages/1RB1RA_1RC1LB/top-blocks.html`.

## November 1, 2026: the shortfall in high valuations comes from the starting tapes, not from the map

The entry of 30 October found that from 60,000 random starts (2 to 4 blocks of 1 to 100, orbits of 2²⁴ super steps)
P(v₂(d₁) ≥ t) at the returns fell short of 2^−t for t ≥ 8 (0.89, 0.85, 0.87, 0.84 at t = 8 to 11, about 3σ), and that
10⁷ starts would settle whether it is real. It is real for that design and comes from its starts; the map's
valuations are geometric. (**heuristic**, `runs/valuation_test.txt`.)

**A faster ensemble** (`c/ensemble_fast.c`, **computed**). The same starts and the same orbits as `c/ensemble.c`
(same xorshift64 and order of draws), run on the periodic tables of `c/superrun.c` (no machine step counts), with the
totals of the returns kept in C: per bit length b of d₁ and valuation s the number of returns, Σ 1/d₁ per b, the same
split by the return's number in its orbit, and consecutive pairs. 0.56 ms per orbit of 2²⁴ super steps instead of
65; 10⁷ orbits in 24 minutes on four cores. `-v` prints exactly what `c/ensemble.c` prints: identical on 6,200 orbits
(50,000 returns) in four designs, and in `tests/test_top.py`. Two differences from `c/superrun.c`, both needed for
random starts: an orbit stops when a tabulated level only ever receives adds (a silent bottom, `lean/Cycles.lean`;
the simplest is a last block of 15, since 15 + 10 = 25 turns back into 15), and a level is tabulated even when only
the top level would stay explicit, since otherwise a two- or three-block start with a silent bottom runs 10¹⁴ super
steps one at a time. `-u` counts a return only if no earlier return of any orbit had the same d₁, the same number of
blocks and the same (up to) three blocks below the top (a 64-bit hash in an open-addressed table, one process).

**The expectation** (`py/top_stats.py fast`, `p_div`). For d₁ of b bits with the density 1/(d₁ ln 2) of the random
model, P(2^t | d₁) = Σ 1/(k 2^t ln 2) over the multiples k·2^t in [2^(b−1), 2^b): 2^−t when t ≪ b, and
1/(2^(b−1) ln 2) for t = b − 1 (the halt). Near-halts, u < 2^c, are s ≥ b − c, so they get the exact expectation
too; the old (2^c/2)/(d₁ ln 2) per return is off by up to 30 % when d₁ is within a few bits of 2^(c+7). The pooled
tests use only b ≥ t + 6.

**The runs** (pooled over d₁ ≥ 2¹⁶ and b ≥ t + 6, observed / expected for 2^t | d₁):

| starts (2²⁴ super steps unless noted) | returns counted | t = 8 | t = 10 | t = 12 | halts, d₁ ≥ 2¹⁶ |
|---|---|---|---|---|---|
| 10⁷, 2–4 blocks of 1–100 (the old design, seeds 1000–1039) | 87,106,740 | 0.901 ± 0.003 | 0.865 ± 0.005 | 0.743 ± 0.012 | 46 / 112.0 |
| the same, `-u` (73,836,550 returns skipped) | 13,267,399 | 0.999 ± 0.007 | 0.984 ± 0.014 | 0.964 ± 0.030 | 26 / 16.6 |
| 10⁷, 4 blocks of 1–100 | 82,828,126 | 1.009 ± 0.003 | 0.977 ± 0.005 | 0.980 ± 0.011 | 117 / 112.6 |
| the same, `-u` (60,179,559 skipped) | 22,603,266 | 0.998 ± 0.006 | 0.987 ± 0.011 | 0.987 ± 0.023 | 41 / 27.6 |
| 10⁷, 2–4 blocks of 1–10⁴ | 82,246,414 | 1.000 ± 0.003 | 1.006 ± 0.006 | 1.002 ± 0.012 | 155 / 109.9 |
| 10⁷, 2–8 blocks of 1–10⁶ | 70,690,020 | 1.000 ± 0.002 | 0.998 ± 0.004 | 0.995 ± 0.008 | 89 / 86.7 |
| 10⁵ of 10¹⁴, the old design | 1,626,302 | 0.940 ± 0.015 | 0.900 ± 0.031 | 0.929 ± 0.062 | 1 / 1.1 |
| the same, `-u` (614,542 skipped) | 1,016,806 | 0.969 ± 0.019 | 0.969 ± 0.038 | 1.04 ± 0.08 | 0 / 0.7 |
| 10⁵ of 10¹⁴, 2–4 blocks of 1–10⁴ | 1,528,219 | 0.995 ± 0.016 | 1.027 ± 0.032 | 1.07 ± 0.06 | 1 / 1.1 |
| 2·10⁵ of 10¹⁴, 2–8 blocks of 1–10⁶ | 2,727,309 | 0.988 ± 0.010 | 1.006 ± 0.019 | 1.004 ± 0.039 | 3 / 1.7 |

The errors are √(expected), which assumes independent returns; that is exactly what fails in the old design.

**What happened in the old design.** Fresh seeds reproduce the shortfall at 36σ (t = 8), but it is lumpy: by the
return's number k in its orbit the ratio at t = 8 runs from 0.26 (k = 18) to 5.7 (k = 19, +35σ), with swings of both
signs at every t, which a smooth property of the map would not give. m = 2 is drawn a third of the time and two blocks
of 1 to 100 make only 10⁴ tapes, so each is drawn about 330 times; and orbits from different starts merge (in 20,000
orbits, 10 % of the returns with d₁ ≥ 2¹⁶ repeat an earlier (S, d₁); over 10⁷ orbits `-u` skips 85 % of all
returns). The run therefore weights a limited set of histories by large, uneven factors, and the σ above mean
nothing for it. With each return counted once the ratios are 1.00 at t = 4 to 8 and 0.96 to 0.99 at t = 9 to 12
(1.2 to 1.6σ each, and not independent of each other); the starts that neither repeat nor merge (blocks up to 10⁴ or
10⁶) give 0.995 to 1.006 for t ≤ 12 with errors of 0.2 % to 1.2 %. The long orbits, with d₁ up to about 2⁵⁰, agree:
in the band d₁ ≥ 2⁴⁰ the wide starts give 0.975 to 1.003 for t ≤ 10 (within 1.1σ) and the old design with `-u` 0.95
to 1.01. On the halts themselves the old design was low above 2¹⁶ (46 against 112); once repeats are removed every
run is at 1.0 to 1.6 times the model there, on counts of 26 to 155.

Two small things remain. The `-u` runs of the narrow designs sit 1 % to 5 % low at t = 9 to 11, each within 2σ;
the key cannot catch two merged orbits whose tables have absorbed different numbers of levels, so some repeats
remain, and the wide starts show nothing of the kind. And with the narrow starts and no `-u`, consecutive returns are
correlated (P(next s ≥ 8 | this s ≥ 6)·2⁸ = 0.68); in the wide starts the same number is 1.05 (on about
2,600 pairs expected) and the other pair statistics are within 1 % of independence.

**What it means.** The one systematic departure from the random model found on 30 October does not survive: at a
return the valuation of d₁ is geometric to within about 1 % for t ≤ 12, at every size of d₁ the runs reach (up to
about 2⁵⁰), from starts that do not repeat. So the odds of a future halt stay at about 5·10⁻²⁵ (heuristic, the
entry of 30 October), with no extra factor in either direction, and a deterministic bound on v₂(d₁) at a return, the
second partial result suggested there, gets no support from the ensemble: whatever would rule out 2⁸⁰ | d₁ at the
next return has to come from the particular orbit, not from a tendency of the map. The blank-tape orbit itself
starts from the narrow tape (1, 6), but it is one orbit; what the narrow designs show is that small starts merge, not
that they avoid high valuations.
