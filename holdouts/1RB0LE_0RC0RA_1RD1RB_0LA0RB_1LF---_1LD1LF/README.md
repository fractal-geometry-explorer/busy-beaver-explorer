# 1RB0LE_0RC0RA_1RD1RB_0LA0RB_1LF---_1LD1LF

bbchallenge id 72026, group G08 (two-sided sqrt growth). Whether it halts from blank tape is **open**. Pages:
[`explainer.html`](../../pages/holdouts/1RB0LE_0RC0RA_1RD1RB_0LA0RB_1LF---_1LD1LF/explainer.html), [`proof-status.html`](../../pages/holdouts/1RB0LE_0RC0RA_1RD1RB_0LA0RB_1LF---_1LD1LF/proof-status.html), both built from
[`status.json`](status.json).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LE |
| B | 0RC | 0RA |
| C | 1RD | 1RB |
| D | 0LA | 0RB |
| E | 1LF | --- |
| F | 1LD | 1LF |

## What it does

A bouncer: both ends grow like the square root of the step count, and each side is a sequence of a few kinds of
unit in an order with no visible period.

**Where it can halt.** Only in E reading a 1. E is entered only from `A>1` (0LE), so the machine halts exactly when
`1 A>1` occurs. In the first 10^8 steps E is entered 12,501,222 times, always onto a 0 (`c/haltwatch.c`).

**Right side** (`py/snapshots.py 2e7 R 100`): runs `(01)^k` each followed by a single 0,

    (10)^5 (01)^21 0 (01)^12 0 (01)^12 0 (01)^12 0 (01)^12 0 (01)^12 0 (01)^12 0 (01)^3 0 (01)^12 0 ...

with k = 12 most of the time, 3 or 21 now and then; near the right end (the youngest part) also 9, 15, 18, and the
end is one long growing run, `... (01)^3 0 (01)^126 (10)^16 1 D>0` at step 2·10^7.

**Left side**: units `000 (110100)^k 110 (010011)^j 01` with k in {3, 6}, j in {4, 7}, e.g.

    A>0 0110011010011 000 1101 000 (110100)^3 110 (010011)^4 01 000 (110100)^6 110 (010011)^4 01 ...

## What is proved (Lean)

Only the generated `lean/Blank.lean`: the halting configurations, no halt in 10^4 steps (kernel) and 10^7
(`native_decide`).

## Computed / observed

- No halt in 10^9 steps (`tools/c/triage.c`).
- The halt-entry counts (`c/haltwatch.c`) and the unit sequences (`py/snapshots.py`).

## Open, and next steps

- Find the rule by which the long run at the right end is cut into runs of 3, 12, 21 (and the matching rule on the
  left). If it is a substitution, the tape is described for all time by a fixed point, and non-halting reduces to
  checking that no unit boundary produces `1 A>1` when the head passes it.
- Once the units are known, prove the single-unit crossings with symtm and the end behaviour as rules.

## Deciders tried (F11, 13 November 2026)

None closes. Each reaches a halting configuration in its abstraction, which says nothing about halting.

- n-gram CPS (`tools/c/ngramcps.c`), equal widths on both sides: a halting local configuration is reached with plain up to width 24, history 1 up to width 24, history 2 up to width 24, history 3 up to width 24, LRU history up to width 11 (larger widths ran out of the 150 s or 60 million configuration budget).
- n-gram CPS with every cell tagged by its position mod p: fails for p = 2 up to width 20, p = 3 up to width 20, p = 4 up to width 20, p = 6 up to width 20.
- n-gram CPS where each side also carries the state of a small automaton that has read that side from the far end (every automaton with up to 3 states on both sides, or 4 states on one side), with position mod 1..4 and widths 4, 6, 8: no closed set without a halt in all 120 parameter sets.
- Run-length windows (the K nearest runs of equal macro cells on each side, run lengths kept exactly below T and mod M above): fails for all 72 parameter sets (cells of 1 to 4 bits, K = 2, 4, 6, T = 2, 4, M = 1, 2, 4).
- Two-automaton closed tape language by SAT (a deterministic automaton reading each side inward, n states each, CaDiCaL): no solution for n = 2..7; n = 8 not finished in 150 s.

## Where a halt can come from

`lean/Route.lean` (kernel, written by `py/route.py`): `halt_route`, two steps before any halt the machine is in one
of: D with 1 two left, 1 left, 0 under the head.

