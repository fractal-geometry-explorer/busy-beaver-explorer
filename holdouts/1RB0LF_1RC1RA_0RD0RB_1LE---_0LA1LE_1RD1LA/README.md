# 1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA

bbchallenge id 90097. **Reported to halt** (about 10^55 steps) by an external Rocq proof, busycoq pull request 60 (Yeyito, 7 Nov 2026, `verify/Halt_1RB0LF_1RC1RA`), which we have not compiled (275 core-hours of `native_compute` jobs). We cross-checked its map against ours (`py/pr60_prefix.py`, `py/pr60_end.py`): its state A(a, b) is our round P((a-6)/2, b); its first 2,000,000 map steps appear in order in our orbit; and from its final round (22, 56*2^85 - 286) both maps halt, at a = 28*2^85 - 6. The middle of the orbit (about 10^25 returns) rests on that proof alone, so `decision` stays `open` here until it is compiled or merged upstream.

Our own result: it is a Lean theorem (`halts_iff_H`, `lean/Map.lean`) that the machine halts iff the orbit of S(13) under a map F on four tape shapes reaches a doubling round with no 1s left; no hit in our 10^8 returns.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LF |
| B | 1RC | 1RA |
| C | 0RD | 0RB |
| D | 1LE | --- |
| E | 0LA | 1LE |
| F | 1RD | 1LA |

## What it does

From step 110 the run passes again and again through

    S(X) = 0^inf 1^X 1110 B> 0^inf        (the head in B on the cell after 1110)

with X = 13, 29, 45, 137, 185, 217, 249, 345, 409, 437, ... (161 returns in 2·10^9 steps, X = 9,265 at step
1,994,919,517). Between two returns the machine does a fixed computation on X, so the whole run is the orbit of 13
under a map f, `X -> f(X)`.

Inside one return the head builds a block of pairs `10` (written `a`) at the left end of the 1s and doubles it by a
zig-zag: `a^k 1^m` becomes `a^(2k+3) 1^(m-2k-3)`, k = 3, 9, 21, 45, 93, ... (Lean: `double`, `S_rounds`). One round of the zig-zag is

    L (10)^(j+1) (1111)^i F> 1 0 1^(m+2) R   ->   L (10)^j 1^(4i+4) F> 1 0 1^m R      (8i+6 steps)

When the doubled block no longer fits in the remaining 1s the round stops in the middle (the overflow, below),
and after at most a few smaller doubling chains the tape is S(f(X)).

`c/reset_map.c` computes f directly (run from S(X) to the next S(Y)). Facts it shows:

- f(X) − X depends on X modulo small powers of 2 and on the position of X between doubling thresholds: e.g. for
  X = 3,037..3,100 it repeats +36, +75, +40, +37 (period 4); in the orbit the increment is constant for long
  stretches (+34 ×23, +33 ×77, ...) and changes at thresholds.
- Halting points: S(X) halts before returning for X = 0, 9, 30, 68, 75, 168, 295, 357, 738 (X ≤ 1,200), and
  for X = 3,010 and 3,036. Non-returning in 3·10^8 steps: X = 41, 52, 63, 132, 273, 558, 1131. Both lists roughly
  double (9, 30, 75, 168, 357, 738; 132, 273, 558, 1131).

The machine halts iff the orbit of 13 hits a halting point (or a non-returning point that halts later). That is ## The overflow, and the whole map

When a round runs out of ones the tape is

    O(p, i, r) = 0^inf 1^6 0 (10)^p (1111)^i F> 1 0 1^r 0 1 0^inf      (p pairs left, i zigs done, r < 2)

and the leftover pairs are swept back to the left end two at a time (each two pairs become a unit `1110`). Every
F-at-the-left-end moment of the run is one of

| name | tape |
|---|---|
| S(x) | `0^inf 1^x 1110 B> 0^inf` |
| P(k, m) | `0^inf F> 0 0 (10)^k 1^m 0 1 0^inf` |
| Q(u, n) | `0^inf F> 0 0 (10)^3 (1110)^u 1^n 0 1 0^inf` (n odd) |
| T(u, v) | `0^inf F> 0 0 (10)^3 (1110)^u 1111 0 (10)^v 0 1 0^inf` (v ≥ 1) |

with the rules (each proved in Lean for all values of the counts):

| from | to |
|---|---|
| S(x), x ≥ 6 | P(3, x) |
| P(k, m), m ≥ 2k+3 | P(2k+3, m−2k−3) |
| P(k, 0) | halt |
| P(k, 1) | S(2k+7) (k odd), Q(k/2, 3) (k even) |
| P(k, 2) | T((k−1)/2, 1) (k odd), S(2k+9) (k even) |
| P(k, 3+2i+r), r < 2, i ≤ k−1 | O(k−1−i, i, r) |
| O(2q+1, i, 0), O(2q+1, i, 1) | P(2q+6, 4i+2), T(q, 2i+3) |
| O(2q+2, i, 0), O(2q+2, i, 1) | Q(q+1, 4i+7), S(4q+4i+17) |
| O(0, i, 0), O(0, i, 1) | S(4i+7), S(4i+13) |
| Q(u, n), n ≥ 9 | P(2u+9, n−9) |
| Q(u, 1), Q(u, 3), Q(u, 5), Q(u, 7) | S(4u+13), Q(1, 4u+7), P(6, 4u+6), S(4u+15) |
| T(u, v) | Q(1, 4u+2v+9) |

Example: S(137) → P(3,137) → P(9,128) → P(21,107) → P(45,62) → [O(15,29,1)] → T(7,61) → Q(1,159) → P(11,150) →
P(25,125) → P(53,72) → [O(18,34,1)] → S(185).

Halting points of one return (6 ≤ X ≤ 1,300): X = 9, 30, 68, 75, 168, 295, 357, 738 (and 3,010, 3,036). Points
that never come back to S: X = 41, 52, 63, 132, 273, 558, 1131, ...: from S(41) the run enters
Q(1,71) → P(11,62) → P(25,37) → P(12,70) → P(27,43) → Q(3,87) → ... → Q(5,103) → ..., a loop whose counts grow by
fixed amounts for ever (so these points do not halt; not formalised).

## What is proved

- **Lean, kernel (`lean/Map.lean`): halts iff the orbit hits a round with no ones.** The nodes `s x` = S(x+6),
  `p a m` = P(a+3, m), `q u c` = Q(u+1, 2c+1), `t u v` = T(u, v+1) and the map `F` are Lean definitions (the table
  above); `F_sem` proves that each value of `F` is where the machine goes in at least one step, and `F = none` only
  at `p a 0`, where it halts. Then
  - `halts_iff`: the machine halts from blank tape iff the orbit of `s 7` (S(13), reached at step 110) under `F`
    reaches `none`;
  - `halts_iff_H`: iff the orbit reaches a node `p a 0`.
  Only the standard axioms (no `native_decide`).
- Lean, kernel (`lean/Overflow.lean`, generated by `py/overflow.py`): the overflow rules O → P/Q/T/S, the rules of
  Q and T, the rounds P(k, 0..2), and `intro3` (the start of a round with only 3 ones); `lean/Map.lean` restates
  them on the named shapes (`r_odd0` ... `r_t`, `r_over`, `overflow_sem`, `r_double`).
- Lean, kernel (`lean/Doubling.lean`): the doubling phase in closed form (`double`, `chain`, `S_rounds`), and
  `blank_to_S13`.
- Lean: `orbit_kernel`, the first 100,000 nodes of the orbit (about 3,900 returns, up to S(407,853)) do not halt
  (kernel); `orbit_native`, the first 10^7 nodes (about 299,000 returns, up to S(34,793,745)), by `native_decide`.
- Computed (C, `c/orbit.c`, the map F transcribed): 10^8 returns (4.6·10^9 nodes, 6 s), X reaches
  15,198,325,533, no halt. Long stretches climb by exactly +100 per return; some returns take long excursions
  through P, Q and T (up to 6.4·10^8 nodes) before S comes back.
- Cross-check (C, `c/reset_map.c`, a direct simulation): f(X) agrees with F for all 1,281 values 6 ≤ X ≤ 1,300 that
  return or halt within 2·10^7 steps.
- Lean (`lean/Blank.lean`, generated): the halting configurations; no halt in 10^4 steps (kernel), 10^7
  (`native_decide`).

## Open

Whether the orbit of s 7 under `F` ever reaches a node `p a 0`. This is a Collatz-like question about one explicit
map; nonhalting would need an invariant of the orbit that keeps it away from the halting rounds.

## For later

- Look for structure in the orbit: the long +100 stretches are runs of one fixed path through the table; describe
  them as an affine map and accelerate (the C iteration could then go much further).
- Formalise nonhalting for the non-returning points (S(41), ...): a parametrised loop of nodes whose counts grow.

  simulation) and look for an invariant residue or for a hit.
- Classify the non-returning points (41, 52, ...): do they halt later, or settle into another pattern?

## Reproduce

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA/lean/check.sh
python3 holdouts/1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA/py/overflow.py > lean/Overflow.lean
gcc -O2 -o orbit holdouts/1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA/c/orbit.c && ./orbit 100000000 10000000
gcc -O2 -o reset_map holdouts/1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA/c/reset_map.c
./reset_map 0 1200 300000000          # f(X), HALT or TIMEOUT for each X
./reset_map 13 13                     # 13 29 255: the first return of the run from blank tape
./tokrun 1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA 400000000 a=10,b=1110 LR   # the tape at extension events
python3 holdouts/1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA/py/rules.py > lean/Rules.lean
. /etc/profile.d/lean.sh && holdouts/1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA/lean/check.sh
```

## Pages

- [`pages/holdouts/1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA/explainer.html`](../../pages/holdouts/1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA/explainer.html)
- [`pages/holdouts/1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA/proof-status.html`](../../pages/holdouts/1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA/proof-status.html)
