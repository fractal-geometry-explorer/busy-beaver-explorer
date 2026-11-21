# 1RB0RF_0LC1RE_---1LD_1LE0LB_0RF0LD_1RD1RA

bbchallenge id 55875. A Collatz-like map on C(e) = 0^inf 1 E> 0 (01)^e: odd e goes to (3e+7)/2 (proved in Lean for every odd e); even e takes a halving cascade, and e = 2^k - 6 halts. The blank run passes C(4), C(17), ..., C(70796) by step 9.4·10^9.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RF |
| B | 0LC | 1RE |
| C | --- | 1LD |
| D | 1LE | 0LB |
| E | 0RF | 0LD |
| F | 1RD | 1RA |

## What it does

`C(e) = 0^inf 1 E> 0 (01)^e 0^inf`, `P(a,b) = 0^inf 111 (0111)^a 01 E> 0 (01)^b 0^inf`.

**Proved** (`lean/Macro.lean`, `odd_step`): for every i, `C(2i+1) -> C(3i+5)`, i.e. odd `e -> (3e+7)/2`:
`C(2i+1) -> P(i,2)` (`enter`, `pack`), `P(a+1,b) -> P(a,b+3)` (`round`, 6b+10 steps), `P(0,b) -> C(b+3)` (`finish`).

**Proved, even e, first stage** (`lean/Even.lean`, `even_start`): for every i, `C(2i+4)` reaches
`Y(i) = 0^inf E> 1 1 0 (10)^i 1 1 0 0 (10)^(i+4) 0^inf`: `enter`, then `even_pack` (F packs `(0101)^(i+3)` into
0111 words), then `half0` and i halving rounds (`half1`, `half`, induction `halving`: each 0111 on the left becomes
one 10 on each side of the marker 1100). From Y(i) the next pass packs the 10s in pairs, so the continuation depends
on the parity of i: i even is e ≡ 0 (mod 4), i odd is e ≡ 2 (mod 4) (which halves again: the cascade).
For i = 2w the run then packs the right run into 0111 words and E, going left, turns each into three more 10s of the
right run (`absorb_1011`: `L 1011 E> 110 (10)^b -> L E> 110 (10)^(b+3)`) and takes in single 10s (`absorb_10`);
the left part (words 1101 and 10) is absorbed the same way with a sweep per word. These rules are proved; chaining
them into the full e ≡ 0 (mod 4) map is not done.

**Simulated** (`c/phasemap.c`, e = 1..300): even `e`:

| e | next |
|---|---|
| ≡ 0 mod 4, e ≥ 8 | (3e+6)/2 |
| ≡ 6 mod 8 | (3e+12)/2 |
| ≡ 2 mod 8 | halving cascade, no single formula (18→41, 74→101, 90→167) |
| 2^k − 6 (2, 10, 26, ..., 1018) | **halts** |

Blank orbit (C(4) at step 67): 4, 17, 29, 47, 74, 101, 155, 236, 357, 539, 812, 1221, 1835, 2756, 4137, 6209,
9317, 13979, 20972, 31461, 47195, 70796 (step 9,357,982,502).

## Even branch, second stage (simulation, 21 November 2026)

With `Y(i, j) = 0^inf E> 110 (10)^i 1100 (10)^j 0^inf` (so `C(2i+4)` reaches `Y(i, i+4)`, `even_start`), the next
`C` or `Y` configuration, found by direct simulation and checked for every 2 <= i <= 120 and j in {0, 1, 2, 5, 8, 13,
30, 61} (`tools/collatz/` triage, not proved):

| Y(i, j) | next |
|---|---|
| i = 2w, j = 2u | C(3w + 3u + 3) |
| i = 2w, j = 2u + 1 | Y(w + u + 1, w + u + 1) |
| i = 4w + 1 | Y(2w, j + 2w + 2) |
| i = 8m + 7, m >= 1 | C(12m + 14 + j) |
| i = 8m + 3 | recursive (another halving); i = 2^k - 5 (3, 11, 27, 59, ...) halts for every j |

So every even e is decided by these rows except when the cascade reaches i = 8m + 3 (or the exception i = 7), which is
where the 2-adic recursion of the e = 2 (mod 8) branch lives. Closing that row would give the whole map, and with it a
big-integer iteration of the orbit far past C(70796).

## The even branch is a stack machine (simulation, 21 November 2026)

The recursive row above is a push. Write a tail as a list τ = (c₀, c₁, …) of counters and

* `X(a; τ) = 0^inf E> 1 (10)^a [0 (10)^c₀] [0 (10)^c₁] … 1 0^inf`,
* `Y(a, b; τ) = 0^inf E> 1 (10)^a 1100 (10)^b [0 (10)^c₀] … 1 0^inf`

(so `C(e)` reaches `X(e + 1; ())`, and the table's `Y(i, j)` is `Y(i + 1, j − 1; ())`). Each step below goes from one
of these configurations to the next one with the head at the left end; every rule was checked by direct simulation
on 16 random points of its class (a ≥ 4, b ≥ 4, c ≥ 6; `fast.py` / `fit4.py` style sampling, not proved):

| from | condition | to |
|---|---|---|
| `X(a; ())` | a even | `C(3a/2 + 2)` |
| `X(a; ())` | a odd | `Y((a − 3)/2, (a + 1)/2; ())` |
| `X(a; c::τ)` | a even | `Y(a/2 − 2, a/2 + c + 1; τ)` |
| `X(a; (c))` | a odd | `C((3a + 3)/2 + c)` |
| `Y(a, b; τ)` | a even | `Y(a/2 − 2, a/2; (b + 2)::τ)`: **push** |
| `Y(a, b; ())` | a odd, b even | `Y((a + b + 3)/2, (a + b − 1)/2; ())` |
| `Y(a, b; ())` | a odd, b odd | `C(3(a + b)/2 + 3)` |
| `Y(a, b; c::τ)` | a odd, b odd | `Y((a + b)/2 + 1, (a + b)/2 + c; τ)`: **pop** |
| `Y(a, b; (c))` | a odd, b even | `C((3a + 3b + 5)/2 + c)` |
| `Y(0, 2; τ)` | any τ | **halts** (17 steps) |

So halving a pushes a counter, and the counters come back one at a time when a is odd. The cases where an odd a meets a
tail of two or more counters and b is even (or X, odd a, two or more counters) are not closed: there the run crosses
several counters in one pass, and the outcome depends on their parities (for `X(a; (c₀, c₁))`, a odd: c₁ odd gives
`C(3a/2 + c₀ + 3c₁/2 + 2)`, c₁ even gives `Y((a + 1)/2 + c₀ + c₁/2, (a − 1)/2 + c₁/2; ())`). The small cases a < 4 are
not tabulated either. Halting configurations reached from blank-like starts are `Y(0, 2; (8, 16, 32, …))`, the
2^k − 6 values above. Next step for a halts-iff: close the multi-counter pass (an induction over τ), then prove each
row with symtm, with τ as an abstract tape where it is passed through.

## Halting

Only C0 halts; C is entered only from B0 (0LC): halts iff `0 B> 0`. CTL K = 3..6: halts remain; n-gram CPS fails;
no invariant mod 2..12.

## Notes for later

- Finish the even branches from Y(i) (`lean/Even.lean`): for i = 2w, `0^inf E> 110 (1010)^w 1100 (1010)^(w+2)`
  becomes (symbolic run) `0^inf 0 1 (1101)^(w-1) 110 101010 (1011)^(w+2) E> 110 10`, then w+2 `absorb_1011`
  rounds, three `absorb_10`, then one sweep per 1101 word on the left (symbolic runs: the first,
  `L 1101 110 E> 110 (10)^(b+1)` -> `L 110 (10)^3 E> 110 (10)^b 1`, puts a trailing 1 on the right; the later ones,
  `L 1101 110 E> 110 (10)^(b+1) 1` -> `L 110 E> 110 (10)^(b+4) 1`, keep it). At the left end
  (`0^inf 0 1 110 E> 110 (10)^b 1`) the run does not finish directly but starts another packing pass, so even
  e ≡ 0 (mod 4) has a second level; this is where to continue. For i odd the 10s cannot be paired and a
  second halving starts (the e ≡ 2 mod 8 cascade, probably a recursion on the 2-adic valuation of e + 6).
- With the whole map proved, the blank orbit gives a kernel-checked lower bound far past 10^10 steps.

## Pages

- [`pages/holdouts/1RB0RF_0LC1RE_---1LD_1LE0LB_0RF0LD_1RD1RA/explainer.html`](../../pages/holdouts/1RB0RF_0LC1RE_---1LD_1LE0LB_0RF0LD_1RD1RA/explainer.html)
- [`pages/holdouts/1RB0RF_0LC1RE_---1LD_1LE0LB_0RF0LD_1RD1RA/proof-status.html`](../../pages/holdouts/1RB0RF_0LC1RE_---1LD_1LE0LB_0RF0LD_1RD1RA/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RF_0LC1RE_---1LD_1LE0LB_0RF0LD_1RD1RA/lean/check.sh
```
