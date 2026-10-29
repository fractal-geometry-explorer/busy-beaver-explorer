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
