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
