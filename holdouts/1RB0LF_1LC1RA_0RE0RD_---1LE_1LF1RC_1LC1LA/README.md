# 1RB0LF_1LC1RA_0RE0RD_---1LE_1LF1RC_1LC1LA

bbchallenge id 165234. One of the six-state holdouts whose halting from blank tape is open (group G10). Family: **two-region bouncer with a Collatz-like reset**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LF |
| B | 1LC | 1RA |
| C | 0RE | 0RD |
| D | --- | 1LE |
| E | 1LF | 1RC |
| F | 1LC | 1LA |

## What it does

At the moments the head, in state A, stands on the blank cell right of the tape, the tape is `(10)^x 1^y` (y odd).
One sweep (left to the pairs and back) removes two pairs and adds six 1s:

    (10)^(x+2) 1^(2y+1) A>   --8y+18 steps-->   (10)^x 1^(2y+7) A>

When the pairs run out the tape is a solid block `Z(t) = 1^t A>` (x even: t = y + 3x; x odd: t = y + 3x + 2), and
a reset follows:

- `t = 2k+6` even: one pass gives `(10)^(k+1) 1^7`, and the sweeps run again.
- `t = 2k+7` odd: the head makes `C> 0 1^(t+7)` at the left end and runs **doubling rounds**. Write
  `R(a,c) = C> 0 1 (01)^a 1^c` and `I(m,i,c) = 1 (01)^m A> 0 1 (01)^(2i) 1^c`. A round starts
  `R(a+1, c+2) -> I(a, 0, c+2)`; each step moves a pair across, `I(m+1, i, c+2) -> I(m, i+1, c)`; a full round ends
  `I(0, i, c+4) -> R(2i+4, c)`, so the left block goes 0, 2, 6, 14, 30, ... pairs (`2^(r+1) - 2` after r rounds).
  The last round ends in one of: `R(a+1, 1)` **halts** (D reads blank tape); `I(m+1, i, 1) -> (10)^m 1^(4i+5)` (back
  to the bouncer); `I(0, i, 1) -> Z(4i+4)`; `I(0, i, 3) -> R(2i+3, 0) -> C> 0 1^(4i+10)`, the rounds start over (this
  happens for t = H_j - 2 and at most once).

Following the counts, an odd block halts iff `t + 2s + 11 = 2^(s+3)` for some s, i.e.
`t = H_j = 2^(j+1) - 2j - 7` (3, 17, 47, 109, 235, 489, 999, ...). From blank tape (= Z(0)):
`Z(0) -> Z(19) -> Z(44) -> 67 -> 99 -> 115 -> 190 -> 288 -> 433 -> 478 -> 720 -> 1081 -> 1572 -> 2359 -> 3236 -> ...`

## What is proved (Lean, kernel unless said otherwise)

- `lean/Leaves.lean` (written by `py/gen_reset.py` with `bbtools.symtm.prove`): the 13 leaf rules above, for all
  parameter values.
- `lean/Reset.lean` (by hand): the rules restated on the configurations `Zc`, `Wc`, `Rc`, `Ic`; the inductions
  (`i_iter`: j steps of a round, `w_to_z`: all sweeps, `chain_sem`: all rounds); the blocks t <= 5 by evaluation;
  the map `F` on states `z t` (= `1^t A>`) and `rs d` (= `C> 0 1^(2d+4)`, a restart) with `F_sem`: `F s = some s'`
  means the machine goes from s to s' (at least one step), `F s = none` means it halts from s. Then
  - `halts_iff : HaltsFromBlank ↔ ∃ n, orbitFrom (.z 0) n = none`, and `halts_iff_44` for the orbit of `z 44`;
  - `F_none_iff`: `F s = none ↔ InH s`, with `InH (z t) := ∃ s, t + 2s + 11 = 2^(s+3)` and
    `InH (rs d) := ∃ s, d + s + 4 = 2^(s+2)`;
  - **`halts_iff_H : HaltsFromBlank ↔ ∃ n s, orbitFrom (.z 44) n = some s ∧ InH s`**.
  Axioms: propext, Classical.choice, Quot.sound only.
- `lean/Orbit.lean`: no halting state in the first 300 resets of the orbit of 44 (kernel), 10,000 (`native_decide`).
- `lean/Rules.lean`: the round-1 sweep rules (`rule0`, `rule1`) from `bbtools.cycles`.

## Status

**Open, Collatz-like**, now as a theorem: the machine halts iff one explicit orbit of a computable map hits the
sparse set H. Heuristically it does not (one halting value per doubling band, the orbit grows about 1.3x per reset).
Proving that the orbit misses H for ever is a number-theory question of Collatz type; no invariant (mod anything)
is known that would exclude it.

## Evidence and checks

- `py/lean_map.py N NSIM`: the map F of Lean transcribed; compared with the first-round fitted map (`py/m2map.py`)
  and with the closed form of H for t < N, and with direct simulation from Z(t) for t < NSIM (no mismatch for
  N = 100,000, NSIM = 300).
- `py/check_map.py N`: the fitted map against direct simulation.

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LF_1LC1RA_0RE0RD_---1LE_1LF1RC_1LC1LA/lean/check.sh      # about 35 s
cd holdouts/1RB0LF_1LC1RA_0RE0RD_---1LE_1LF1RC_1LC1LA/py && python3 lean_map.py 100000 300 && python3 m2map.py 44 30
python3 py/gen_reset.py > lean/Leaves.lean        # regenerate the leaf rules (from the folder)
```

## Pages

- [`pages/holdouts/1RB0LF_1LC1RA_0RE0RD_---1LE_1LF1RC_1LC1LA/explainer.html`](../../pages/holdouts/1RB0LF_1LC1RA_0RE0RD_---1LE_1LF1RC_1LC1LA/explainer.html)
- [`pages/holdouts/1RB0LF_1LC1RA_0RE0RD_---1LE_1LF1RC_1LC1LA/proof-status.html`](../../pages/holdouts/1RB0LF_1LC1RA_0RE0RD_---1LE_1LF1RC_1LC1LA/proof-status.html)
