# 1RB1RE_1LC1LD_---1LA_1LB1LE_0RF0RA_1LD1RF

bbchallenge id 116538. One of the six-state holdouts whose halting from blank tape is open. The run reduces
(proved in Lean) to a Hydra-like iteration `X -> floor(3X/2) + 5` whose epochs end by c mod 4; epoch 4's end
decides on a parity of a number with about 10^13 digits.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RE |
| B | 1LC | 1LD |
| C | --- | 1LA |
| D | 1LB | 1LE |
| E | 0RF | 0RA |
| F | 1LD | 1RF |

## What it does

Stop the machine whenever the head, in state F, stands just right of everything written. From step 139 on the tape
is then always

    P c u x  =  0^inf 1^c (01)^u 0 0 (10)^x F> 0^inf          (u = 2 or 3)

- **Bounce** (`bounce`, `bounce_iter`): `L (01)^(x+2) 0 0 (10)^(y+1) F>` becomes `L (01)^x 0 0 (10)^(y+4) F>` in
  4y+18 steps: each trip of the head moves two `01` pairs from the middle into three `10` pairs on the right.
- **Phase** (`phase`): when the middle is used up the head bites 4 ones off the left run (`glue2`, `glue3`) and
  rebuilds the middle. With `X = x + u + 4`:

      P (c+4) u x  ->  P c (2 + X mod 2) (3 floor(X/2) - 1)

  so in terms of X it is the Hydra-like map `X -> floor(3X/2) + 5`.
- **Epoch**: starts at `P c 3 5`, makes `floor(c/4)` phases, then `r = c mod 4` and u decide (`end*`, x >= 16):

  | r | u = 2 | u = 3 |
  |---|---|---|
  | 0 | halt | `P (2x+5) 3 5` |
  | 1 | `P (2x+5) 3 5` | halt |
  | 2 | halt | halt |
  | 3 | `P (2x+8) 3 5` | `P (2x+10) 3 5` |

From blank tape (`py/epochs.py`):

    epoch 0   P 3 3 5                 step 139       0 phases, r = 3
    epoch 1   P 20 3 5                step 364       5 phases, r = 0, u = 3
    epoch 2   P 297 3 5                              74 phases, r = 1, u = 2
    epoch 3   P 459271258863231 3 5   ~10^28 steps   114,817,814,715,807 phases, r = 3: a new epoch for sure
    epoch 4   P c4 3 5                c4 = 2x+4+2u has about 2*10^13 digits, c4 mod 4 = 2(x+u) mod 4

## Status

Open, and very likely out of reach of computation (a Hydra-like cryptid that is expected to *halt*).

Proved in Lean (`lean/Phase.lean` on top of the generated `lean/Rules.lean`, all for all parameters, kernel-checked):

- `phase`, `phases`: the phase rule, k phases.
- `end_some`, `end_none`: the epoch-end table above.
- `halts_iff : HaltsFromBlank ↔ ∃ k, epochs k = none`, where `epochs 0 = some 3`,
  `epochs (k+1) = (epochs k).bind ends` and `ends c` runs `c/4` phases from `(u, x) = (3, 5)` then the table.
- `epochs_first`: `epochs 1 = some 20`, `epochs 2 = some 297`, `epochs 3 = some 459271258863231`
  (`decide +kernel`); `epochs_4`: epoch 3 ends in a new epoch (459271258863231 mod 4 = 3). So no halt before the
  end of epoch 4.

Evidence: `py/epochs.py check 400` compares the model with an exact accelerated simulator (`py/fastsim.py`) on the
first 400 P configurations (into epoch 3, about 10^114 steps): no mismatch. `py/epochs.py ends` runs all eight
epoch-end cases at x = 1000..1002. The C simulator finds no halt in 10^9 steps.

Heuristic: the end of epoch 4 is a halt if x+u is odd at the end of epoch 3 (r = 2), or if it is even and epoch 4's
last u is 2. With fair-coin parities: halt there with probability 3/4, eventually with probability 1 (r = 3 is
always followed by r = 0 or 2, r = 2 always halts). The halting step count would have about 10^(2*10^13) digits.

What is open: the parity of x+u after 1.15*10^14 phases of `X -> floor(3X/2)+5` from X = 12. Computing it needs the
low `N - n` bits of the n-th iterate, numbers of up to about 4*10^13 bits, about 10^27 bit operations; no shortcut
is known (as for Hydra/Antihydra).

### Next steps

- A smarter way to get the parity of x+u at the end of epoch 3 (2-adic structure of `floor(3X/2)+5`)? Nothing
  short of the full iteration is known for maps of this kind.

## Pages

- [`pages/holdouts/1RB1RE_1LC1LD_---1LA_1LB1LE_0RF0RA_1LD1RF/explainer.html`](../../pages/holdouts/1RB1RE_1LC1LD_---1LA_1LB1LE_0RF0RA_1LD1RF/explainer.html)
- [`pages/holdouts/1RB1RE_1LC1LD_---1LA_1LB1LE_0RF0RA_1LD1RF/proof-status.html`](../../pages/holdouts/1RB1RE_1LC1LD_---1LA_1LB1LE_0RF0RA_1LD1RF/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RE_1LC1LD_---1LA_1LB1LE_0RF0RA_1LD1RF/lean/check.sh
python3 holdouts/1RB1RE_1LC1LD_---1LA_1LB1LE_0RF0RA_1LD1RF/py/epochs.py            # the epochs
python3 holdouts/1RB1RE_1LC1LD_---1LA_1LB1LE_0RF0RA_1LD1RF/py/epochs.py check 400  # model vs simulator
python3 holdouts/1RB1RE_1LC1LD_---1LA_1LB1LE_0RF0RA_1LD1RF/py/epochs.py ends       # the eight end cases
python3 holdouts/1RB1RE_1LC1LD_---1LA_1LB1LE_0RF0RA_1LD1RF/py/rules.py > holdouts/1RB1RE_1LC1LD_---1LA_1LB1LE_0RF0RA_1LD1RF/lean/Rules.lean
```
