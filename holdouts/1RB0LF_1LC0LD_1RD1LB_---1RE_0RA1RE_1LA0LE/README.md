# 1RB0LF_1LC0LD_1RD1LB_---1RE_0RA1RE_1LA0LE

bbchallenge id 15252, a six-state holdout of group G05 (growth class fixed/sqrt). **Open.** Lean (kernel) proves
that the machine follows an exact block machine and halts *if and only if* that block machine reaches a left block
of exactly four 1s with nothing but single 1s to its right (`halts_iff`, `halts_iff_four`). The run is a
doubly exponential counter: from the configurations `O(N) = 1^N F>0 0 1^3` it goes to `O(N')` with N' roughly
2^(√N / 3), and an epoch halts exactly when N lies in a sparse set `H = {2^(n+4) - 2n - 10}` (the *if* part is proved
in Lean for every n, `outer_halts`). The orbit from blank tape is 10, 27, 60, 118, 254, 514, 1014, 2106, 17220,
8534636888060, ...: none of these is in H.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LF |
| B | 1LC | 0LD |
| C | 1RD | 1LB |
| D | --- | 1RE |
| E | 0RA | 1RE |
| F | 1LA | 0LE |

## What it does

**The tape.** Every macro configuration has the head in state F on a *gap* `0 0`, with a block of X ones on its left
and blank tape beyond. Right of the gap the tape is a row of blocks of 1s, each followed by one 0:

    0^∞ 1^X  F>0 0  (1 0)^a  [mid]  (1 0)^b  [tail]  0^∞

with runs of *units* (single 1s), `mid` either nothing, an empty block (an extra 0) or an even block `1^(2q+2) 0`, and
`tail` nothing or an odd block `1^(2q+3)`. This is `Q = ⟨X, a, mid, b, tail⟩` in `lean/Macro.lean`.

**The moves** (cell rules written by `bbtools.symtm.prove`, `lean/Rules.lean`; k is the number of units in front
of the first block that is not a unit):

- *walk*: F crosses a unit `1 0` to the left in 2 steps, so the units travel freely between the gap and a block;
- *round* (X >= 3, a block Y >= 2 after the units): X -> X - 2, Y -> Y - 2, two more units; 6k + 18 steps
  (X = 0: the same without the left block, 6k + 14). So a left block and a block on the right wear each other down
  two by two, leaving units behind;
- *merge* (X >= 5, an empty block after the units): X -> X - 4, and the k units, the 0 and the next block Z become
  one block 2k + Z + 5 (6k + 20 steps). After the rounds against an odd block 2q + 3, this makes the block
  2(2q + 3) + 5: a *doubling pass*;
- *restart* (X = 0 or 3 at an empty block): the head runs to the left end and back, the units and the next block Z
  become the new left block X' = 2k + Z + 6, and the block after Z loses one 1 (8k + Z + 19 steps); at the end of
  the tape the new left block is 2k + Z + 4 and a new block `1^3` is written: an *outer configuration*;
- X = 2 gives X = 5 (15 steps); X = 1 walks over as a unit.
- **halt**: X = 4 with nothing but units right of the gap: D reads a 0 after 6k + 17 steps.

`mstep : Q → MS` (`lean/Macro.lean`) is one such move with its exact cost; `mstep_sound` and `mstep_halt`
(`lean/Sound.lean`) prove that the machine follows it.

**The emergent behaviour: a doubly exponential counter.** An *epoch* runs from an outer configuration
`O(N) = 1^N F>0 0 1^3` to the next. Example, O(2106):

1. *Doubling passes.* The block 3 grows 3, 11, 27, 59, ..., 2043 (b -> 2b + 5), each pass eating b + 3 ones of X,
   until X = 82 is left.
2. *Setup.* The X = 2 move and a restart leave 76 units in front of a stored block 1963, with X = 21.
3. *Inner epochs.* With X_j = 24·2^j - 3 (21, 45, 93, 189, ...), a fresh small block goes through its own doubling
   passes 6, 18, 42, ..., eating one unit per merge, until a restart makes X_{j+1} = 2X_j + 3. Each inner epoch uses
   up j + 4 units and costs 1152·4^j - 216·2^j + 10 steps (found from the run, checked for every j < 400).
4. *End.* When the units run out the inner block and the stored block merge (2148), the passes go on with what is
   left of X (4301, 8607), and the epoch ends at O(17220), after 2.5·10^8 steps.

With u units after the setup there are about √(2u) inner epochs, so N' is about 24·2^√(2u), and u is a fair part of
N: N' ≈ 2^(c√N) with c about 1/3. The next values: 17220 -> 8534636888060 (about 6.5·10^25 steps), and the next one
has on the order of a million bits.

**Where it halts.** `halts_iff_four`: the machine halts iff the block machine reaches X = 4 with only units on the
right. In an epoch this happens when a doubling pass leaves exactly four 1s on the left: a pass against the block
2q + 3 takes X = x + 2q + 7 to x + 1 (`pass`) and halts if X = 2q + 6 (`pass_halt`). With the blocks 3, 11, 27, ...
(q = 0, 4, 12, ...) the n-th pass ends at 4 exactly when **N = T_n = 2^(n+4) - 2n - 10** for some n
(6, 20, 50, 112, 238, 492, 1002, 2024, 4070, ...): `outer_halts` (Lean, kernel) proves that each such O(N) halts.
By computation, for 5 <= N <= 3000 the epoch from O(N) halts iff N is one of these. Nearly all odd N go to a power
of two minus 4 (27 -> 60), and from 60 on the orbit stays even.

So the machine halts iff the outer orbit 10, 27, 60, ... ever hits H (and the converse rests on the computed
pattern, not on a proof). H has one element per doubling of N, so if N behaves like a random number of its size
the chance that it lies in H is about 1/N: already about 2^(-43) for N = 8534636888060, and N grows doubly
exponentially, so the chance of any later hit is negligible.

## Status and evidence

**Lean, kernel only.**
- `lean/Rules.lean` (generated by `py/gen_rules.py`): the 14 cell rules (walk, round, roundz, merge, restart,
  restart3, tail0, tail1, tail30, tail31, cback, two1, two2, haltcfg), each for every value of its variables.
- `lean/Macro.lean`: the configurations `Q`, `cfg`, and the block machine `mstep` with exact costs.
- `lean/Sound.lean`: `mstep_sound` (`mstep s = .go s' n → steps n (cfg s) = some (cfg s')`), `mstep_halt`.
- `lean/Reduce.lean`: `init_cfg` (blank tape reaches O(10) in 102 steps); the invariant `InvQ` is kept and
  excludes the `stuck` cases (`inv_next`); **`halts_iff : HaltsFromBlank ↔ ∃ n, mrun n m0 = .halt`**;
  `mstep_halt_iff`; **`halts_iff_four`**.
- `lean/Outer.lean`: `rounds_tail`, `pass` (a doubling pass: X = x + 2q + 7 -> x + 1, block 2q + 3 -> 2(2q + 4) + 3),
  `pass_halt`, `T_closed`, **`outer_halts`: `1^N F>0 0 1^3` halts for N = 2^(n+4) - 2n - 10**, every n.

**Lean, `native_decide`** (`lean/MacroRun.lean`): `macro_runs`, `blank_runs_macro`: 2·10^7 macro steps of the
block machine, no halt, so no halt in the first 191,906,825,348,151 steps (`runN_sound`, kernel, says the runner
computes a run of the machine). `lean/Axioms.lean` prints the axioms: only the standard ones, plus the
`native_decide` axiom for `blank_runs_macro`.

**Computed (trusted).**
- `py/macro.py check 1e8`: the Python block machine agrees with the machine, cell for cell and step for step, at all
  15,261 macro configurations of the first 10^8 steps; `py/macro.py run 20000000` gives the step count in
  `MacroRun.lean`.
- `py/outer.py 9`: the outer orbit with batched rounds (and inner epochs jumped by the closed form): O(10) at step
  102, then 27 (401), 60 (2,196), 118 (10,760), 254 (43,454), 514 (181,170), 1014 (721,486), 2106 (2,911,484),
  17220 (251,528,266), 8534636888060 (about 6.54·10^25 steps). The first eight epochs need no jump or one; the
  ninth jumps 35 inner epochs, all with j < 400 where the closed form was checked.
- For 5 <= N <= 3000 the epoch from O(N) halts iff N ∈ H.

**Heuristic.** The inner-epoch closed form beyond j = 400; the claim that H is the only way to halt for all N; and
the estimate that the orbit avoids H forever (chance of a hit about 1/N per epoch).

**Open.** Whether the orbit ever hits H. N' depends on N through the remainder left by the doubling passes and the
number of inner epochs, a Collatz-like map of N; nothing visible excludes an exact hit.

## Reproduce

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LF_1LC0LD_1RD1LB_---1RE_0RA1RE_1LA0LE/lean/check.sh   # about 2 minutes
python3 holdouts/1RB0LF_1LC0LD_1RD1LB_---1RE_0RA1RE_1LA0LE/py/macro.py check 1e8     # block machine vs machine
python3 holdouts/1RB0LF_1LC0LD_1RD1LB_---1RE_0RA1RE_1LA0LE/py/macro.py run 20000000  # the number in MacroRun.lean
python3 holdouts/1RB0LF_1LC0LD_1RD1LB_---1RE_0RA1RE_1LA0LE/py/outer.py 9             # the outer orbit, ~10 minutes
python3 holdouts/1RB0LF_1LC0LD_1RD1LB_---1RE_0RA1RE_1LA0LE/py/gen_rules.py           # regenerate lean/Rules.lean
```

## Layout

| path | what it is |
|---|---|
| `lean/Machine.lean`, `lean/Blank.lean` | the machine and bounded runs (generated) |
| `lean/Rules.lean` | the cell rules (generated by `py/gen_rules.py`) |
| `lean/Macro.lean` | the configurations and the block machine `mstep` |
| `lean/Sound.lean` | `mstep_sound`, `mstep_halt` |
| `lean/Reduce.lean` | the invariant, `halts_iff`, `halts_iff_four` |
| `lean/Outer.lean` | doubling passes and `outer_halts` |
| `lean/MacroRun.lean` | the block machine run 2·10^7 macro steps with `native_decide` |
| `lean/Axioms.lean` | the axioms of the main theorems |
| `py/macro.py` | the block machine in Python, checked against the machine |
| `py/outer.py` | the outer orbit, with batched rounds and jumped inner epochs |
| `py/gen_rules.py` | writes `lean/Rules.lean` |

## Pages

- [`pages/holdouts/1RB0LF_1LC0LD_1RD1LB_---1RE_0RA1RE_1LA0LE/explainer.html`](../../pages/holdouts/1RB0LF_1LC0LD_1RD1LB_---1RE_0RA1RE_1LA0LE/explainer.html)
- [`pages/holdouts/1RB0LF_1LC0LD_1RD1LB_---1RE_0RA1RE_1LA0LE/proof-status.html`](../../pages/holdouts/1RB0LF_1LC0LD_1RD1LB_---1RE_0RA1RE_1LA0LE/proof-status.html)

## For later

- Prove the inner epoch in Lean, for every j and every number of units: X_j = 24·2^j - 3 goes to X_{j+1} with
  j + 4 units used. With `pass` this gives the whole epoch as a function `Φ` with `O(N) -> O(Φ(N))`, so that
  halting becomes, in Lean, *the orbit of 10 under Φ meets H*. The same proof would show that halting outside H is
  impossible.
- Then compute Φ on the tenth value (on the order of a million bits) and later ones directly from the formula, and study Φ
  mod powers of two: an exact hit needs N' ≡ -2n - 10 (mod 2^(n+4)), which could perhaps be ruled out 2-adically.
