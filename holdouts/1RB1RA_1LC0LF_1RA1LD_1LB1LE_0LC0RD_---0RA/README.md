# 1RB1RA_1LC0LF_1RA1LD_1LB1LE_0LC0RD_---0RA

bbchallenge id 129887. One of the six-state holdouts whose halting from blank tape is open (group G07, family: **recursion on words over two 3-cell tokens (nested counters, a = c b b blocks eaten from inside)**).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RA |
| B | 1LC | 0LF |
| C | 1RA | 1LD |
| D | 1LB | 1LE |
| E | 0LC | 0RD |
| F | --- | 0RA |

## What it does

The tape has three parts. At the left (growing) end sits a **periodic block**, `(1^5 0 1^2 0)^k` (at other times
`(1^8 0)^k`, another word of 9 cells). Each visit of the left end adds three
cells to it, one copy every three visits. To its right lies a **disordered middle**, runs of 1s of lengths
divisible by 3 separated by `0` and `110`; it keeps changing and eats the periodic block from the inside: the
block grows steadily, then at rare moments is swallowed almost entirely (14 times in the first 10^9 steps, last
at step 401,140,791, when at least 749 copies went at once). At the right, a short end region stopped growing early.

Snapshot at step 999,899,483 (`a = 111110110`, `b = 110`): `0 1 b a^2938 b^4 a b^11 1^6 b 1^3 b 1^3 b 1^9 a ...`

## Status

Open. Trusted: at every visit of the left end the tape is a word over `110` and `111` (2·10^10 steps), and the
recursion below gives the next word at 95% of the visits. Lean: the halting configurations and 10^7 steps (`lean/Blank.lean`), and shift rules for the head crossing
the periodic block (in state D, and in state E) and runs of `110`, for any length (`lean/Shifts.lean`, kernel). Simulation: no
halt in 10^11 steps (`tmrun`, about 30 minutes).
No halt in 10^12 steps (`c/mrun.c` of the 1RB1LE_0LC1RE_---1LD_0RD1LA_0RF1RF_1RA0LB folder, a direct
simulator on blocks of 16 cells; the tape then spans about 1.6 million cells).

## Second look: when the block collapses

Following the copies of `1^5 0 1^2 0` at the left end at every visit of the left end in state D (up to 10^9 steps):
the block grows by exactly one copy every three visits and then is swallowed at once. The block had, just before
each collapse, 11, 9, 84, 36, 135, 100, 36, 324, 36, 36, 260, 999 and 36 copies (steps 29,371 to 419,367,273). The
value **36 recurs five times**, so the collapses are not random: the middle region probably triggers a collapse when
a carry inside it arrives, and the block size at that moment is set by the region's own clock. After a collapse the
left end shows `(1^8 0)^k` for a while (another word of 9 cells) before `1^5 0 1^2 0` takes over again.

## Third look: the tape is a word over two tokens, a visit is a recursion on it

Cut the tape into tokens of three cells, `b = 110` and `c = 111`. Call a *visit* the moment the head stands in B on
the blank cell left of the tape. **At every visit the whole tape is a word over b and c**: all 74,198 visits of the
first 2·10^10 steps (`c/wcheck.c`; the longest word has 83,005 tokens). The periodic block is `a = c b b`
(`111 110 110`), the runs of 1s of length divisible by 3 are runs of c.

Each visit turns the word w into a word F(w), one token longer unless the visit reaches the right end. For
w = b X the next word is b V(X), with

    (1) V(b X)           = c c X                  the visit ends at the first b it is handed
    (2) V(c c b c^n b Y) = c b c c b^n V(Y)       these two pass the visit on to the rest of the word
    (3) V(c b c^n b Y)   = c b b b^n V(Y)
    (4) V(c c c ...)     : not decoded

Rules (1) to (3) give the next word at 2,239 of the 2,361 visits between the 8th and 3·10^7 steps and never a
wrong one (`py/words.py run 3e7`); at the other 122 the rest of the word starts with `c^m`, m = 3, 4, 6, 8, 10,
11 or 12. Those are the long visits that rewrite the word deep inside ("the middle eats the block") or run to the
right end and make the word several tokens longer.

What the rules say: `a = c b b` is rule (3) with n = 0, so the periodic block passes every visit on unchanged, and
the word behind it lives through a cycle of three visits, `b b b b b Y -> c c b b b b Y -> c b c c c c b Y ->
c b b  b b b b  V(Y)`: one more copy of `a`, one b fewer, and **one visit for the rest Y**. So the rest of the word
is the same system running three times slower, and so on inwards: nested counters, as in the twins
`1RB1LF_1LC1RB_...` of this group. The block collapses when the b's between two levels run out and a level meets
a `c c c`.

**The halt.** F is entered only from B reading 1, B only from A reading 0 (then the cell on its left is a 1 just
written) or from D reading 0. So the machine halts exactly when **C reads a 1 and the three cells to its left
are `0 1 0`**. In 2·10^10 steps the machine was one cell from this 12,171 times (C reads 1, D reads 0, B reads 1),
each time with a 1 in place of the first 0.

**A conjecture that would decide it.** For every word w over b and c, the visit on w (blank tape on both sides) leads
to a visit on a word over b and c again. Checked for all 32,766 words of at most 14 tokens and for the words
starting with b up to 16 tokens, 81,918 words in all (`py/words.py all 16`): never a halt, never another token. The word grows by up to
164 tokens when the visit reaches the right end. If this holds for all words the machine never halts.

**Attempts at a proof.** Finite automata reduction (`py/far.py`, `py/wfar2.py`) with, on the right side, an
automaton that remembers the nearest 6 to 15 cells and that everything beyond is a word over b, c in a known
phase: no proof; the same with windows on the left (up to 12 cells and the distance mod 3) and with run-length
windows. Reason, as far as understood: in the middle of a visit the part of the word behind the head has already
been rewritten by the inner levels, and what the head does on its way back depends on that; a window does not see it.

## Next steps

* Decode rule (4): the visits on `c c c ...`. With it F is a recursion on words, and an exact simulator on words
  (cost per visit: the depth of the recursion, not the length of the tape) reaches far beyond 10^11 steps.
* Prove the conjecture by induction on the word, with the rules as lemmas (each rule is a statement "if the visit
  on Y gives V(Y), then the visit on `c b c^n b Y` gives ..."): the pieces between two crossings of the border of
  Y are straight runs that `bbtools.symtm` can prove; the right end needs its own rules.
* The automaton that a certificate needs has to know the level structure of the word (which `b^n` belongs to
  which level), not a window.

## First look

Growth class **fixed/sqrt** (left: sqrt, exponent 0.539; right: fixed,
exponent 0.433). After 1,000,000,000 steps: 63,728 cells visited (37,689 left of the
start, 9,934 right), 51,851 ones.

- left, step 975,564,704: `D>0 1 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 `
- left, step 991,221,611: `D>0 1 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 `

## Deciders tried (F11, 13 November 2026)

None closes. Each reaches a halting configuration in its abstraction, which says nothing about halting.

- n-gram CPS (`tools/c/ngramcps.c`), equal widths on both sides: a halting local configuration is reached with plain up to width 20, history 1 up to width 16, history 2 up to width 15, history 3 up to width 14, LRU history up to width 5 (larger widths ran out of the 150 s or 60 million configuration budget).
- n-gram CPS with every cell tagged by its position mod p: fails for p = 2 up to width 16, p = 3 up to width 16, p = 4 up to width 16, p = 6 up to width 16.
- n-gram CPS where each side also carries the state of a small automaton that has read that side from the far end (every automaton with up to 3 states on both sides, or 4 states on one side), with position mod 1..4 and widths 4, 6, 8: no closed set without a halt in all 120 parameter sets.
- Run-length windows (the K nearest runs of equal macro cells on each side, run lengths kept exactly below T and mod M above): fails for all 72 parameter sets (cells of 1 to 4 bits, K = 2, 4, 6, T = 2, 4, M = 1, 2, 4).
- Two-automaton closed tape language by SAT (a deterministic automaton reading each side inward, n states each, CaDiCaL): no solution for n = 2..8; n = 9 not finished in 150 s.

## Where a halt can come from

`lean/Route.lean` (kernel, written by `py/route.py`): `halt_route`, two steps before any halt the machine is in one
of: D with 0 two left, 1 left, 0 under the head.

## Pages

- [`pages/holdouts/1RB1RA_1LC0LF_1RA1LD_1LB1LE_0LC0RD_---0RA/explainer.html`](../../pages/holdouts/1RB1RA_1LC0LF_1RA1LD_1LB1LE_0LC0RD_---0RA/explainer.html)
- [`pages/holdouts/1RB1RA_1LC0LF_1RA1LD_1LB1LE_0LC0RD_---0RA/proof-status.html`](../../pages/holdouts/1RB1RA_1LC0LF_1RA1LD_1LB1LE_0LC0RD_---0RA/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RA_1LC0LF_1RA1LD_1LB1LE_0LC0RD_---0RA/lean/check.sh
cd holdouts/1RB1RA_1LC0LF_1RA1LD_1LB1LE_0LC0RD_---0RA
gcc -O2 -o /tmp/wcheck c/wcheck.c && /tmp/wcheck 2e10     # every visit shows a word over 110, 111 (2 minutes)
cd py && python3 words.py run 3e7                           # rules (1)-(3) against the run
python3 words.py all 16                                     # the conjecture on all short words (10 minutes)
python3 wfar2.py 1RB1RA_1LC0LF_1RA1LD_1LB1LE_0LC0RD_---0RA R 9 tokfar 4e6    # one of the FAR attempts
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0RF_1LC1RD_1LA1LC_1RA1RE_0RB0LD_---0LC`](../1RB0RF_1LC1RD_1LA1LC_1RA1RE_0RB0LD_---0LC/README.md): rename A→C, B→A, C→B, D→D, E→E, F→F and exchange left and right; it is this table started in state B, in a mirror

<!-- end of related machines -->
