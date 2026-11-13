# 1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD

bbchallenge id 97525. Its tape is an alternating block and a solid block whose lengths trade back and forth; each pass rewrites one block into the other.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RC |
| B | 1LC | 1RE |
| C | 1RA | 1LD |
| D | 0LC | 0LA |
| E | 1RF | 1RD |
| F | --- | 0RD |

## What it does

Stop the run when the head reaches a new cell (`a = 10`):

    97,915,409  D>0 a^2 1 a^802 1^338      (left end)
    97,921,865  A>0^2 a^806 1^336           (left end)
    98,376,215  1^2 a 1^604 a^672 C>0       (right end)
    98,837,298  A>0^2 a^540 1^874           (left end)
    99,362,025  C>0^2 a^722 1^513           (left end)

Two long blocks, alternating and solid, whose lengths trade; each rewrite costs about x^2 steps, width ~ t^(1/3).
Same shape as the three `1RB1RD_0LC1RA_..._1RF0LD_---0RE` machines; exact rules not worked out.

## Halting

F0 halts; F is entered only from E0 (`1RF`), so a halt needs `E>0 0`. In the first 10^8 steps F was entered
83,257 times, always on a 1 (`c/sstat.c`). Open.

## The frame map in Lean

Frames (blank outside; `X` the head in state X on the next cell; `u^v` v copies of u, so
`11^L` is 2L ones; a frame counts only where the head turns round):

- `z`: `1^L 10^j C 1^R`
- `y`: `1^L A 10 10^j 1^R`
- `w`: `1^L C 00 10^j 1^R`
- `u`: `1^L 10^j 1 A 00 1^R`
- `Z`: `1110 1^L 10^j C 1^R`
- `Y`: `1110 1^L A 10 10^j 1^R`
- `W`: `1110 1^L C 00 10^j 1^R`
- `U`: `1110 1^L 10^j 1 A 00 1^R`

The map, as `next` in `lean/Phases.lean`:

```lean
def next : Ph → Option Ph
  | .z 0 0 0 => some (.w (0) (0) (4))
  | .z (l + 1) 0 0 => some (.y (l) (0) (2))
  | .z l (j + 1) 0 => some (.u (l) (j) (2))
  | .z 0 0 (r + 1) => some (.w (0) (0) (r + 1))
  | .z 0 (j + 1) (r + 1) => some (.w (0) (j + 1) (r + 1))
  | .z 1 0 (r + 1) => some (.w (0) (0) (r + 3))
  | .z 1 1 1 => none
  | .z 1 1 2 => some (.Y (1) (0) (1))
  | .z 1 1 3 => some (.U (2) (0) (2))
  | .z 1 1 (r + 4) => some (.Y (3) (0) (r + 1))
  | .z 1 2 1 => some (.Z (4) (0) (0))
  | .z 1 2 2 => some (.Y (2) (0) (2))
  | .z 1 2 (r + 3) => some (.U (3) (0) (r + 1))
  | .z 1 (j + 3) (r + 1) => some (.W (4) (j) (r + 1))
  | .z (l + 2) 0 (r + 1) => some (.y (l) (0) (r + 1))
  | .z (l + 2) (j + 1) (r + 1) => some (.y (l) (j + 1) (r + 1))
  | .y 0 0 0 => some (.w (0) (0) (4))
  | .y 0 (j + 1) 0 => some (.u (0) (j) (2))
  | .y 0 j 1 => some (.u (0) (j) (2))
  | .y 0 j (r + 2) => some (.z (0) (j + 1) (r + 1))
  | .y (l + 1) 0 0 => some (.u (l) (0) (2))
  | .y (l + 1) (j + 1) 0 => some (.u (l) (j + 1) (2))
  | .y (l + 1) j 1 => some (.u (l) (j + 1) (2))
  | .y (l + 1) j (r + 2) => some (.z (l) (j + 2) (r + 1))
  | .w 0 0 0 => some (.w (0) (0) (4))
  | .w (l + 1) 0 0 => some (.y (l) (0) (2))
  | .w l 0 1 => none
  | .w l 0 2 => some (.y (l + 1) (0) (1))
  | .w l 0 3 => some (.u (l + 2) (0) (2))
  | .w l 0 (r + 4) => some (.y (l + 3) (0) (r + 1))
  | .w l 1 0 => none
  | .w l 1 1 => some (.z (l + 4) (0) (0))
  | .w l 1 2 => some (.y (l + 2) (0) (2))
  | .w l 1 (r + 3) => some (.u (l + 3) (0) (r + 1))
  | .w l 2 0 => some (.z (l + 4) (0) (0))
  | .w l (j + 3) 0 => some (.w (l + 4) (j) (1))
  | .w l (j + 2) (r + 1) => some (.w (l + 4) (j) (r + 1))
  | .u 0 0 r => some (.w (0) (0) (r + 4))
  | .u (l + 1) 0 r => some (.y (l) (0) (r + 2))
  | .u l (j + 1) r => some (.u (l) (j) (r + 2))
  | .Z 0 0 0 => some (.u (2) (0) (2))
  | .Z 0 (j + 1) 0 => some (.u (2) (j + 1) (2))
  | .Z 0 0 (r + 1) => some (.y (0) (1) (r + 1))
  | .Z 0 (j + 1) (r + 1) => some (.y (0) (j + 2) (r + 1))
  | .Z (l + 1) 0 0 => some (.Y (l) (0) (2))
  | .Z (l + 1) (j + 1) 0 => some (.U (l + 1) (j) (2))
  | .Z 1 0 (r + 1) => some (.u (2) (0) (r + 1))
  | .Z 1 (j + 1) (r + 1) => some (.y (5) (j + 1) (r + 1))
  | .Z (l + 2) 0 (r + 1) => some (.Y (l) (0) (r + 1))
  | .Z (l + 2) (j + 1) (r + 1) => some (.Y (l) (j + 1) (r + 1))
  | .Y 0 j 0 => some (.y (0) (1) (2 * j + 4))
  | .Y 0 j 1 => some (.y (0) (1) (2 * j + 6))
  | .Y 0 j (r + 2) => some (.w (3) (j + 1) (r + 1))
  | .Y 1 0 0 => some (.u (2) (1) (2))
  | .Y 1 (j + 1) 0 => some (.u (2) (j + 2) (2))
  | .Y 1 j 1 => some (.u (2) (j + 2) (2))
  | .Y 1 j (r + 2) => some (.z (2) (j + 3) (r + 1))
  | .Y (l + 2) 0 0 => some (.U (l + 1) (0) (2))
  | .Y (l + 2) (j + 1) 0 => some (.U (l + 1) (j + 1) (2))
  | .Y (l + 2) j 1 => some (.U (l + 1) (j + 1) (2))
  | .Y (l + 2) j (r + 2) => some (.Z (l + 1) (j + 2) (r + 1))
  | .W 0 0 0 => some (.u (2) (0) (2))
  | .W (l + 1) 0 0 => some (.Y (l) (0) (2))
  | .W l 0 1 => none
  | .W l 0 2 => some (.Y (l + 1) (0) (1))
  | .W l 0 3 => some (.U (l + 2) (0) (2))
  | .W l 0 (r + 4) => some (.Y (l + 3) (0) (r + 1))
  | .W l 1 0 => none
  | .W l 1 1 => some (.Z (l + 4) (0) (0))
  | .W l 1 2 => some (.Y (l + 2) (0) (2))
  | .W l 1 (r + 3) => some (.U (l + 3) (0) (r + 1))
  | .W l 2 0 => some (.Z (l + 4) (0) (0))
  | .W l (j + 3) 0 => some (.W (l + 4) (j) (1))
  | .W l (j + 2) (r + 1) => some (.W (l + 4) (j) (r + 1))
  | .U 0 0 r => some (.u (2) (0) (r + 2))
  | .U 0 (j + 1) r => some (.u (2) (j + 1) (r + 2))
  | .U (l + 1) 0 r => some (.Y (l) (0) (r + 2))
  | .U (l + 1) (j + 1) r => some (.U (l + 1) (j) (r + 2))
```

`lean/Phases.lean` proves every case for all sizes (`next_sound`, from the symbolic runs in `lean/Pieces.lean`),
that the undefined cases `.z 1 1 1`, `.w l 0 1`, `.w l 1 0`, `.W l 0 1`, `.W l 1 0` halt (`none_halts`), `halts_iff` (the machine halts from blank tape
iff the orbit of `Ph.z 0 0 2` reaches one of them), and by `native_decide` that the first 10^8 frames do
not (`no_halt_phases`; about 4.5*10^11 steps).

`py/pieces.py` regenerates both Lean files from the machine: it fits the map (`py/fitlib.py`, frames in `py/spec.py`),
collapses it into cases (`py/tree.py`) and proves each case with `tools/py/bbtools/symtm.py`. `py/framemap.py` is the
fitted map in Python: `verify R`, `real N`, `run K` (checked: `verify 16` with 30,736
frames and `real 5000000` with 48,691 frames, no mismatch).

## Status

Open. Lean (`lean/Blank.lean`): the halting configurations (`step_none_iff`), no halt in 10,000 steps by the kernel, in 10,000,000 by `native_decide`. C: no halt in 10^9 steps (`tools/c/triage.c`) and in 10^15 steps (`c/mrun.c`, exact macro simulation). Lean (`lean/Phases.lean`, on `lean/Pieces.lean` generated by `py/pieces.py`): the whole frame map, 78 cases over 8 tape shapes, for all sizes (`next_sound`); the undefined cases halt (`none_halts`); the machine halts iff the orbit of `Ph.z 0 0 2` reaches one (`halts_iff`); not in the first 10^8 frames (`no_halt_phases`, `native_decide`; about 4.5*10^11 steps). Open: whether the orbit ever gets there.

## First look

Growth class **power/power** (left: power, exponent 0.321; right: power,
exponent 0.347). After 1,000,000,000 steps: 4,302 cells visited (2,289 left of the
start, 1,181 right), 3,792 ones.

- left, step 978,463,966: `A>0 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 `
- left, step 996,611,172: `A>0 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 `
- right, step 971,819,859: `1^3524 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0`
- right, step 993,561,919: `1^2617 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0`






## Pages

- [`pages/holdouts/1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD/explainer.html`](../../pages/holdouts/1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD/explainer.html)
- [`pages/holdouts/1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD/proof-status.html`](../../pages/holdouts/1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD/proof-status.html)






## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD/lean/check.sh
gcc -O2 -o mrun holdouts/1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD/c/mrun.c && ./mrun 1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD 2 1000000000000000
gcc -O2 -I tools/c -o sstat holdouts/1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD/c/sstat.c && ./sstat 1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD 100000000
python3 holdouts/1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD/py/pieces.py && git diff --exit-code holdouts/1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD/lean
python3 holdouts/1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD/py/framemap.py verify 16
```

## Later

- Find the higher-level rule (one sweep or round to the next) and which sizes lead to an undefined case, as was
  done for the all-ones lengths of `1RB1RD_0LC1RA_0RA1LC_1RA1LE_1RF0LD_---0RE`.
