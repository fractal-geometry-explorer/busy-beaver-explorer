# 1RB---_1LC0RF_1RF0LD_0LE1LC_0RC0LC_1RB0RA

bbchallenge id 10753, group G08 (two-sided sqrt growth). Whether it halts from blank tape is **open**. Pages:
[`explainer.html`](../../pages/holdouts/1RB---_1LC0RF_1RF0LD_0LE1LC_0RC0LC_1RB0RA/explainer.html), [`proof-status.html`](../../pages/holdouts/1RB---_1LC0RF_1RF0LD_0LE1LC_0RC0LC_1RB0RA/proof-status.html), both built from
[`status.json`](status.json).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | --- |
| B | 1LC | 0RF |
| C | 1RF | 0LD |
| D | 0LE | 1LC |
| E | 0RC | 0LC |
| F | 1RB | 0RA |

## What it does

A bouncer over a period-2 background. Both ends grow like the square root of the step count; the tape is `1010...`
cut into domains by small defects that move from sweep to sweep.

**Where it can halt.** Only in A reading a 1. A is entered only from `F>1` (0RA), so the machine halts exactly when
`F>1 1` occurs. In the first 10^8 steps A is entered 267,524 times, always onto a 0 (`c/haltwatch.c`). The background
has no two adjacent 1s, so a halt needs a defect.

**The tape** (`py/snapshots.py 1e8 L 400`):

    75183174 E>0 0 (01)^4 0000 (10)^6 1 (10)^4 000 (10)^20 000 (10)^16 000 (10)^26 1 (10)^20 (01)^17 00000 (10)^17 ...
    85674864 E>0 0 (01)^3 (10)^32 1 (10)^16 (01)^5 (10)^20 000 (10)^14 000 (10)^14 000 10 (01)^18 0000 (10)^27 ...

Domains of 3 to about 100 periods; defects `000`, `0000`, a lone extra `1`. No stable block or counter is visible.

## What is proved (Lean)

Only the generated `lean/Blank.lean`: the halting configurations, no halt in 10^4 steps (kernel) and 10^7
(`native_decide`).

## Computed / observed

- No halt in 10^9 steps (`tools/c/triage.c`); density of 1s 0.501.
- The halt-entry counts (`c/haltwatch.c`) and the domain picture (`py/snapshots.py`).

## Open, and next steps

- Classify the defects (how each one is changed when the head sweeps over it in each direction, and what two
  defects produce when they meet). If the set of defect types is finite and closed, a closed-language argument with
  the background as `(10)*` could prove non-halting.
- This is the least structured of the machines in this batch; it was given only a first look.

## Deciders tried (F11, 13 November 2026)

None closes. Each reaches a halting configuration in its abstraction, which says nothing about halting.

- n-gram CPS (`tools/c/ngramcps.c`), equal widths on both sides: a halting local configuration is reached with plain up to width 16, history 1 up to width 14, history 2 up to width 13, history 3 up to width 12, LRU history up to width 2 (larger widths ran out of the 150 s or 60 million configuration budget).
- n-gram CPS with every cell tagged by its position mod p: fails for p = 2 up to width 12, p = 3 up to width 12, p = 4 up to width 12, p = 6 up to width 12.
- n-gram CPS where each side also carries the state of a small automaton that has read that side from the far end (every automaton with up to 3 states on both sides, or 4 states on one side), with position mod 1..4 and widths 4, 6, 8: no closed set without a halt in all 120 parameter sets.
- Run-length windows (the K nearest runs of equal macro cells on each side, run lengths kept exactly below T and mod M above): fails for all 72 parameter sets (cells of 1 to 4 bits, K = 2, 4, 6, T = 2, 4, M = 1, 2, 4).
- Two-automaton closed tape language by SAT (a deterministic automaton reading each side inward, n states each, CaDiCaL): no solution for n = 2..9; n = 10 not finished in 150 s.

## Where a halt can come from

`lean/Route.lean` (kernel, written by `py/route.py`): `halt_route`, two steps before any halt the machine is in one
of: B with 1 under the head, 1 right, 1 two right; C with 0 under the head, 1 right, 1 two right.

