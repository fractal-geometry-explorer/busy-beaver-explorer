# 1RB0RF_1RC1RF_1LD0LE_---1LC_1RA1LE_1LC1RB

bbchallenge id 144815, a BB(6) holdout (group G06). **Family: Collatz-like map on one block length.**

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RF |
| B | 1RC | 1RF |
| C | 1LD | 0LE |
| D | --- | 1LC |
| E | 1RA | 1LE |
| F | 1LC | 1RB |

## What it does

At the end of every pass the whole tape is one block of n ones, with the head in state B on the blank cell just
right of it: **P(n) = `0^inf 1^n B> 0^inf`**. The run from blank reaches P(4) at step 9, then P(8), P(13), P(22),
P(28), P(38), P(45), P(70), P(79), P(121), ... A pass from P(n) takes about 1.3 n² steps.

* **The pass, in general.** Write X(a, b, c) = `0^inf 1^a E> 0 1^b 0 1^c 0^inf`. A pass starts with
  P(n+1) -> X(0, n, 2). Then:
  * b odd: `X(a, b, c) -> X(a+1, b-2, c+1)` down to b = 1, then `X(a+1, 1, c) -> X(0, a, c+3)` (the new middle
    block is (b-3)/2); `X(0, 1, c)` halts (D reads 0).
  * b even: `X(a, b, c) -> X(a+c, b, 0)`, then `X(a, b+2, 0) -> X(a+1, b, 2)` and so on to `X(a', 0, 2)` = P(c+3b/2+2).
    For b = 0 and c odd the pass goes through `Q(m) = 0^inf 1^m F> 0^inf` and once more round.

  With B = b+3, the odd case halves B; the machine halts when B reaches 4. So, from P(n), it halts iff n+2 is a
  power of two. Exactly: P(n) reaches P(f(n)), f(n) = g(n-1, 2), with
  g(0, c) = c+2 (c even) or (3c+9)/2 (c odd), g(2i+2, c) = c+3i+5, g(1, c) = halt, g(2i+3, c) = g(i, c+i+4).
* **Closed form.** With n + 2 = 2^j m, m odd:

| case | f(n) |
|---|---|
| m = 1 (n+2 a power of two) | **halts** (state D reads 0) |
| m = 3, j even, j ≥ 2 | 9·2^(j−1) + 3j/2 + 3 |
| otherwise | 2^j m + (m + 2j − 1)/2 |

For odd n (j = 0) the last line is (3n+5)/2. A pass multiplies n by about 1 + 2^-(j+1).

## The recursion in rule form

As the bbchallenge wiki writes Antihydra's: exact tapes, then rules with exact step counts. A is the name the wiki page
of this machine uses (it is X(0, b, c) above):

    P(n)    := 0^∞ 1^n B> 0^∞
    A(b, c) := 0^∞ E> 0 1^b 0 1^c 0^∞

    0^∞ A> 0^∞      --1-->                            P(1)                 (then A(0, 2); P(4) at step 9)
    P(n)            --n + 3-->                        A(n − 1, 2)          n ≥ 1
    A(2i+3, c)      --2i² + 10i + 13-->               A(i, c + i + 4)
    A(1, c)         --7-->                            HALT                 (D reads 0)
    A(2i+2, c)      --6i² + 19i + 11 + c(4i + 7)-->   P(c + 3i + 5)
    A(0, 2j)        --2j + 2-->                       P(2j + 2)
    A(0, 2j+1)      --4j + 7-->                       A(2j + 2, 1)         (through 0^∞ 1^(2j+3) F> 0^∞)

Each target is the first P or A tape the machine reaches. The rules are the recursion g of `lean/Macro.lean`, proved
(`pstart`, `odd_run` + `odd_end`, `xhalt`, `even_full`, `zero_end_e`, `zero_end_o` + `qstart`, in `xrun`), with the
halts-iff (`halts_iff`); P(4) at step 9 is `blank_P4` (`lean/Pass.lean`). The step counts are proved for the tape
moves the rules are built from (`lean/Rules.lean`: odd round 4i + 11, even round 4i + 7, ...); the totals are their
sums, checked against direct simulation (`py/steps.py`: 4,021 tapes including 61 halting A(1, c), and every P/A tape
of the first 10^8 steps of the run), not stated in Lean. The wiki's A(2x, y) -> A(3x + y + 1, 2) is the even row
followed by the open row. Example: P(14) -> A(13, 2) -> A(5, 11) -> A(1, 16) -> halt takes 17 + 113 + 25 + 7 = 162
steps.

## Status

Open, **reduced in Lean**: the machine halts iff the orbit 4, 8, 13, 22, 28, ... of f reaches an n with n+2 a
power of two. Probviously never.

* Lean (kernel), `lean/Macro.lean`: `pass` (every pass, every n, from `xrun`), `halts_iff` (halts from blank iff
  the orbit of 4 under f reaches `none`), `f_none_iff` (f(n) = none iff n+2 = 2^(j+2)). Built from the 17 symtm
  rules of `lean/Rules.lean` (`lean/rules.py`) and inductions `odd_run`, `even_run`, `even_down`. Older:
  `lean/Pass.lean`, `blank_P4`, `odd_pass`.
* Lean (native): `orbit_10000`, `no_halt_10000`: no halt in the first 10,000 passes.
* Trusted (`py/study.py`): g equals the closed form for n < 200,000; the closed form equals simulated passes for
  n ≤ 3000 (`c/passmap.c`, `py/orbit.py --check`); 200,000 passes from 4 without a halt (n then has 80,223 bits);
  growth e^0.2780 per pass (e^0.2783 predicted for random low bits); the counts of j = v2(n+2) follow 2^-(j+1).
* Heuristic, short argument (not in Lean): f(n) + 2 = 2^k forces j ∈ {2, 3} (9m + 7 = 2^(k+1) or
  17m + 9 = 2^(k+1)), since modulo 2^(j+1)+1 the powers of two are ±2^i; the m = 3 exception never gives a power of
  two. So only about 1.3 values per binary length end the run, and the orbit spends about 2.5 passes per length:
  the chance of a halt from 80,223 bits on is about 2^-80000. No invariant forbidding a halt is known.
* Lean (`lean/Blank.lean`): the halting configurations, no halt in 10⁷ steps; C: no halt in 10⁹ steps.

## For later

* Non-halting would need to control the low bits of the orbit forever (a Collatz-type statement); nothing suggests a
  residue invariant (the j counts look geometric). The j ∈ {2, 3} argument could go into Lean.

## Doucette's form (`lean/Doucette.lean`)

The closed form of the pass is now proved (it was checked numerically before). With D = n + 2 = 2^v (2a + 1):
D' = D + a + v + 2 (`G_rule`), except D = 3·2^v with v even and positive, where D' = (3D + 3v + 10)/2 (`G_three`;
never taken in the first 20,000 passes); a power of two halts (`G_pow2`). `halts_iff_doucette`: the machine halts
from blank tape iff the sequence 6, 10, 15, 24, 30, 40, ... (`Dorb`) reaches a power of two. The five machines of
this family are listed in [`tools/sweep/README.md`](../../tools/sweep/README.md).

## Pages

- [`pages/holdouts/1RB0RF_1RC1RF_1LD0LE_---1LC_1RA1LE_1LC1RB/explainer.html`](../../pages/holdouts/1RB0RF_1RC1RF_1LD0LE_---1LC_1RA1LE_1LC1RB/explainer.html)
- [`pages/holdouts/1RB0RF_1RC1RF_1LD0LE_---1LC_1RA1LE_1LC1RB/proof-status.html`](../../pages/holdouts/1RB0RF_1RC1RF_1LD0LE_---1LC_1RA1LE_1LC1RB/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RF_1RC1RF_1LD0LE_---1LC_1RA1LE_1LC1RB/lean/check.sh
gcc -O2 -o passmap holdouts/1RB0RF_1RC1RF_1LD0LE_---1LC_1RA1LE_1LC1RB/c/passmap.c
./passmap 1 3000 | python3 holdouts/1RB0RF_1RC1RF_1LD0LE_---1LC_1RA1LE_1LC1RB/py/orbit.py --check
python3 holdouts/1RB0RF_1RC1RF_1LD0LE_---1LC_1RA1LE_1LC1RB/py/study.py 200000
python3 holdouts/1RB0RF_1RC1RF_1LD0LE_---1LC_1RA1LE_1LC1RB/py/steps.py     # the rule table and its step counts against direct simulation
```
