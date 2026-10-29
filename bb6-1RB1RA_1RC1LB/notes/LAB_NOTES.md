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
