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
Same shape as the three `1RB1RD_0LC1RA_..._1RF0LD_---0RE` machines. The exact rules are the frame map below; the
epochs they make (growth x4/3, drain x4) are in "Sweeps as jumps".

## Halting

F0 halts; F is entered only from E0 (`1RF`), so a halt needs `E>0 0`. In the first 10^8 steps F was entered
83,257 times, always on a 1 (`c/sstat.c`). At the level of the frame map a halt needs a zigzag to start on one of
five halting rows ("The halting rows" below); with the closed pass map (`lean/Close.lean`) it halts iff the
orbit of `y(3, 0, 5)` lands on one of two lines (`halts_iff_row`). Open.

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

## The recursion in rule form

As the bbchallenge wiki writes Antihydra's: exact tapes, then rules with exact step counts. The families are the
frames of the Lean map (head on the cell after `>`; Z, Y, W, U are z, y, w, u with `1110` at the left end):

    z(l, j, r) := 0^∞ 1^l (10)^j C> 1^r 0^∞
    y(l, j, r) := 0^∞ 1^l A> 10 (10)^j 1^r 0^∞
    w(l, j, r) := 0^∞ 1^l C> 00 (10)^j 1^r 0^∞
    u(l, j, r) := 0^∞ 1^l (10)^j 1 A> 00 1^r 0^∞
    Z(l, j, r) := 0^∞ 1110 1^l (10)^j C> 1^r 0^∞     (Y, W, U alike)

    0^∞ A> 0^∞                --2-->              z(0, 0, 2)
    z(l+2, j, r+1)            --2j + 2-->         y(l, j, r+1)               zig (also Z -> Y)
    y(l+1, j, r+2)            --2j + 3-->         z(l, j+2, r+1)             zag (also Y(l+2, ..) -> Z(l+1, ..))
    z(l+3k, j, r+k+1)         --4k² + 4jk + k-->  z(l, j+2k, r+1)            k zigzag rounds
    w(l, j+2k, r+1)           --6k-->             w(l+4k, j, r+1)            w sweep (also W)
    u(l, j+k, r)              --4k-->             u(l, j, r+2k)              u sweep (also U(l+1, ..))
    z(0, j+1, r+1)            --2j + 4-->         w(0, j+1, r+1)             to w
    y(0, j, r+2)              --2j + 3-->         z(0, j+1, r+1)             to w, at the left end
    y(l+1, j, 1)              --2j + 8-->         u(l, j+1, 2)               to u (also Y(l+2, j, 1) -> U(l+1, j+1, 2))
    w(l, 0, r+4)              --5-->              y(l+3, 0, r+1)             back from w (also W -> Y)
    w(l, 1, r+3)              --6-->              u(l+3, 0, r+1)             back from w (also W -> U)
    u(l+1, 0, r)              --4-->              y(l, 0, r+2)               back from u (also U -> Y)
    z(1, j+3, r+1)            --2j + 24-->        W(4, j, r+1)               new bracket
    Z(1, j+1, r+1)            --2j + 30-->        y(5, j+1, r+1)             bracket dissolves
    Y(0, j, r+2)              --4j + 7-->         w(3, j+1, r+1)             bracket dissolves
    Y(1, j, r+2)              --2j + 3-->         z(2, j+3, r+1)             bracket dissolves
    z(1, 1, 1)                --19-->             HALT
    w(l, 0, 1), w(l, 1, 0)    --5-->              HALT                       (also W(l, 0, 1), W(l, 1, 0))

Every row but the k-round ones is one or a few cases of `next` (`next_sound`, `none_halts`, `init_start` in
`lean/Phases.lean`). The step count of each case is the step number in its piece theorem in `lean/Pieces.lean`
(`next_sound` itself only says some number exists; a halting row adds the halting step); the k-round totals are sums
and are not stated in Lean. The other 49 of the 78 cases (small l, j, r) are left out of the table; in the first 10^7
steps from blank tape they make 14 of the 77,045 moves. `py/rules.py` reads the cases and step counts from the Lean
files and checks them against direct simulation: all 78 cases on 5,832 frames, the table rows with their bracket
variants on 25,957 instances, and every frame of the first 10^7 steps from blank tape. Example: u(11, 0, 3) =
1^12 A> 00 1^3 halts after 4 + 3 + 63 + 18 + 24 + 5 = 117 steps (y(10, 0, 5), z(9, 2, 4), z(0, 8, 1), w(0, 8, 1),
w(16, 0, 1), halt), as direct simulation gives.

## Sweeps as jumps: the closed map

Almost every application of `next` repeats one of a few cases, and the repeats sum in closed form
(`lean/Jump.lean`, for all sizes):

    w(l, j + 2k, r + 1)       --k frames, 6k steps-->               w(l + 4k, j, r + 1)        w_sweep (also W)
    u(l, j + k, r)            --k frames, 4k steps-->               u(l, j, r + 2k)            u_sweep (also U(l + 1, ..))
    y(a + 3k, j, r + 1 + k)   --2k frames, k(4j + 9) + 4k(k-1)-->    y(a, j + 2k, r + 1)        y_zigzag (also Y)

`jump` takes each whole sweep or zigzag at once (the largest k for which every application is still the first
matching case of `next`) and is `next` everywhere else; `jump_sound` proves each jump is that many frames of `next`.
So the run is a sequence of about 10^8 jumps per 1.5·10^14 frames, each jump O(1) arithmetic:
`c/frun.c` does 7·10^7 jumps a second.

The jumps show what the machine does. Write the tape as a solid block `1^l`, an alternating block `(10)^j`, and a
solid block `1^r`. An *epoch* has two phases:

* **growth**: `w(L, e, R)` → `y(L + 3, 0, R - 3)` (or via `u` to `y(L + 2, 0, R)`), a zigzag that turns the left
  block into alternating cells (each round eats 3 of `l` and 1 of `r` and adds 2 to `j`), then a `w` sweep that turns
  them back into a left block 4/3 as long. The left block grows by 4/3 per pass and the right block pays `L/3` per
  pass, so after about `log_{4/3}` of the size the right block runs out in the middle of a zigzag;
* **drain**: from `y(a, j, 1)` the `u` sweep moves the alternating block into the right block (`r = 2j + 4`), and
  the zigzags now run until `r` runs out again, each pass multiplying `r` by about 4 and costing 3r of the left block,
  until the left block is used up and a new growth phase starts with a long right block.

Within a phase the ratios are fixed; what is chaotic is where the phases end, the remainders mod 3 at the crossovers.
The total length grows by a few cells per pass, so the size grows about linearly in the number of jumps
(the right block at a crossover is about J/10 after J jumps) and the steps like J^3.

### The halting rows

`next` is `none` only at `z(1,1,1)`, `w(l,0,1)`, `w(l,1,0)` and their `W` twins. A zigzag ends when `a < 3` or
`r = 1`; it ends with `r = 2` (or 3) left exactly when the two blocks run out together, and then three more frames
and a sweep decide. Lean proves five rows that halt (`lean/Jump.lean`):

| row | route | theorem |
|---|---|---|
| `y(3k+1, 2m, k+2)` | k rounds, `y(1, ., 2)`, `z(0, ., 1)`, `w(0, even, 1)`, sweep to `w(., 0, 1)` | `halt_y` |
| `Y(3k+1, 2m, k+3)` | k rounds, `Y(1, ., 3)`, `z(2, ., 2)`, `y(0, odd, 2)`, `z(0, ., 1)`, `w(0, even, 1)`, sweep | `halt_Y` |
| `y(3k, 2m+1, k+2)` | k rounds, `y(0, odd, 2)`, `z(0, even, 1)`, `w`, sweep | `halt_y0` |
| `y(3k+2, 2m+1, k+2)` | k rounds, `y(2, odd, 2)`, `z(1, ., 1)`, `W(4, even, 1)`, sweep | `halt_y2` |
| `Y(3k, 2m+1, k+2)` | k rounds, `Y(0, odd, 2)`, `w(3, even, 1)`, sweep | `halt_Y0` |

From every frame with all three numbers below 60 (205,943 of them halt within 400 jumps), every halt comes before
the first zigzag or right after a zigzag start in one of these rows (`frun rows 60`). That this holds for all
frames is not proved. In the run from blank tape every zigzag start so far has even `j` (`frun stats`), so only
the first two rows can be met: **the machine halts if a crossover lands on `y(a, 2m, R)` with `a = 3R - 5` or on
`Y(a, 2m, R)` with `a = 3R - 8`** (and `a ≡ 1 mod 3`). Call `d = R - floor(a/3) - 2` (y) or `- 3` (Y) the distance
to the row; `d = 0` halts.

### The run

`c/frun.c` (checked case by case: `frun check`, `py/check_frun.py` against the Lean cases read by `py/rules.py`,
`py/jumps_panel_test.js` for the page's copy):

| jumps | frames | machine steps | frame |
|---|---|---|---|
| 1,000,000,000 | 14,663,127,908,673,683 | 8.1·10^23 | Y(43,889,550, 0, 359,123,705) |
| 10,000,000,000 | 1,466,115,638,078,894,721 | 8.1·10^26 | y(3,138,081,542, 0, 891,798,589) |
| 20,000,000,000 | 5,864,258,929,373,709,319 | 6.5·10^27 | y(2, 1,489,737,902, 5,080,219,723) |
| 50,000,000,000 | 36,651,764,352,175,722,702 | 1.0·10^29 | U(3,885,282,087, 0, 16,263,964,358) |
| 100,000,000,000 | 146,605,789,270,410,448,593 | 8.1·10^29 | u(39,742,276,314, 0, 556,168,540) |

No halt; it was stopped at 100,000,000,000 jumps (1.5·10^20 frames, 8.1·10^29 machine steps), against 3.58·10^22 steps before.
Lean checks the first 10^8 jumps by `native_decide` (`jumps_frames`): no halt in the first 146,530,202,670,678
frames (`no_halt_frames`; Phases.lean had 10^8).

Close calls (zigzag starts with `|d| ≤ 2`, `frun close`): y(10, 0, 6) at jump 30 (d = +1), Y(34, 0, 13) at jump 103 (d = -1), y(139,357, 0, 46,453) at jump 461,762 (d = -1), Y(1,699,306, 0, 566,440) at jump 5,624,455 (d = +2). None at `d = 0`.

### How likely is a halt (heuristic; revised in "Passes" below)

At a crossover the ratio a/(3R) lands somewhere in an interval of fixed relative width, so the chance of `d = 0` is
about c/R per epoch, and `R` is about J/10 while an epoch is about `log J` jumps. Summed, the expected number of
hits up to J grows like `ln ln J`: it diverges, but very slowly. Counting the zigzag starts with `|d| ≤ 16` per
unit of `ln ln J` gives about 1.5 expected hits per unit of `ln ln J` (per value of d); from J = 10 to 100,000,000,000 that
is about 3.6 expected hits and none was seen. If the heuristic is right the machine halts with probability 1, but
the median waiting time is around `ln ln J ≈ 3.7`, i.e. `J ≈ 10^18` jumps, about 10^53 steps: far beyond
any computation. The close calls near `d = 0` are thinner than this rate predicts (8 with `|d| ≤ 3` against about 15),
which might be chance or a hidden obstruction near the rows.

## Passes: the run as a map of one number

A *pass* runs from one zigzag start (`y` or `Y` with `a ≥ 3`, `r ≥ 2`) to the next: a zigzag, a few single frames and
a sweep. Away from the line where both blocks run out together it is one affine map, proved for all sizes in
`lean/Pass.lean` (generated by `py/gen_pass.py`; 13 theorems, each a chain of the jump lemmas with its exact frame
count). Write the zigzag start `t(a, j, r)` with `a = 3q + e`:

    drain   r ≤ q − 1:  t(a, j, r)  →  t(a − 3r + 1, 0, 4r + 2j + 2)        drain_y, drain_Y   (j + 4r − 1 frames)
    growth  r ≥ q + 7:  t(a, j, r)  →  t'(4q + 2j + c, 0, r − q − d)       grow_*             (3q + j/2 + O(1) frames)

| t | e | j even: t', c, d | j odd: t', c, d |
|---|---|---|---|
| y | 0 | y, 2, 1 | y, 5, 4 |
| y | 1 | y, 7, 4 | y, 4, 1 |
| y | 2 | Y, 2, 1 | Y, 5, 4 |
| Y | 0 | y, 5, 1 | y, 8, 4 |
| Y | 1 | y, 11, 5 | y, 8, 2 |
| Y | 2 | `y(5, j + 2q + 2, r − q − 1)` (`grow_Y2`; a one-round zigzag follows) | same |

Only within 6 of the line `r = q` does the run go back to jumps, and every halting row lies there (`d = 0` is
`r − q = 2` for y and 3 for Y). `fast` is the 13 cases, `pass` is `fast` where it applies and `jump` elsewhere,
`pass_sound`: each pass is that many frames of `next`. `passes_frames` runs 10^8 passes from the blank-tape frame by
`native_decide` (about two minutes): **no halt in the first 3,893,676,335,181,895 frames** (`no_halt_passes`;
1.1·10^23 machine steps), against 146,530,202,670,678 frames for 10^8 jumps.

**One number.** In both cases `N = a + r` changes by a few cells only (`+3` for a drain, between −1 and +5 for a
growth), so the state is essentially the fraction `x = a/N`, and a pass is

    x → 4x/3        (growth, x < 3/4)
    x → 4x − 3      (drain,  x > 3/4)

two full branches of slopes 4/3 and 4; Lebesgue measure is invariant, and the histogram of `x` over the run is flat
to three digits (`y` two thirds, `Y` one third of the starts). The epochs above are runs of growth ended by one drain.
A halt needs `x` to land exactly on the branch point 3/4, to the cell: `y(a, 0, r)` with `a = 3r − 5`, or
`Y(a, 0, r)` with `a = 3r − 8`.

`c/prun.c` iterates the pass map with 64-bit sizes and 128-bit frame and step counts, about 5.7 times as fast as
`frun` (about 7.5·10^7 passes a second; one pass is about 5 jumps). Checks: `prun check 20000000000` compares every
fast pass of the first 2·10^10 passes (10^11 jumps) with the same frames taken by frun's jumps, no mismatch; at
10^9 jumps both give frame Y(43,889,550, 0, 359,123,705), 14,663,127,908,673,683 frames and
808,181,051,345,378,964,383,732 steps; `py/pass_panel_test.js` checks the page's copy on 300,000 passes.

### The run of the pass map

`./prun run 4000000000000 10000000000 16` (lines in `c/run_pass.txt`; the run is still going, the file is the state
when this was written):

| passes | frames | machine steps | zigzag start |
|---|---|---|---|
| 10,000,000,000 | 38,941,988,752,206,149,446 | 1.1·10^29 | Y(18,669,849,162, 0, 2,099,341,822) |
| 100,000,000,000 | 3,894,236,934,565,580,464,641 | 1.1·10^32 | y(184,676,324,319, 0, 23,016,354,114) |
| 180,000,000,000 | 12,617,324,367,611,392,880,906 | 6.5·10^32 | y(104,283,617,405, 0, 269,562,505,980) |

No halt in 1.8·10^11 passes (about 9·10^11 jumps, 1.3·10^22 frames, **6.5·10^32 machine steps**), against 8.1·10^29
for the jump map. Zigzag starts within 2 of a halting row, besides the four above: y(58,039,094,419, 0, 19,346,364,807)
at pass 37,259,714,570 (d = −1) and y(123,130,300,774, 0, 41,043,433,591) at pass 79,046,523,555 (d = −2).

### How likely is a halt (revised)

The estimate above took an epoch to last about log J jumps. It does not: a growth pass ends the epoch with chance
1/4 (the drain branch has measure 1/4), so epochs are a bounded number of passes on average, and the chance of a hit
is about 1/(4N) at every pass. With N about 2.08 times the pass count, the expected number of hits grows like
ln(passes), not ln ln J.

The run follows the uniform model at the scale of single cells (`py/near.py` on `c/near_1e11.txt`, the first 10^11
passes, N = a + j + r): 285 zigzag starts within 16 of the boundary against 290 expected, and 84 within 16 of a
halting row against 97 expected (ratio 0.87). That gives a hazard of about 0.22 hits per unit of Σ1/N. Random orbits
of the pass map (`prun rate`, `c/rate.txt`: 4,307 halts, each right after a zigzag start with d = 0, so no halt
avoided the two rows) give between 0.08 and 0.47 by size; the map is not injective, orbits merge, and those samples
are far from independent. With 0.22: Σ1/N from pass 1,000 to 10^11 is 9.1, so about 2 hits were expected and none
came (chance about 14%); each further factor 10 of passes adds about 0.24 expected hits; the median halt would be
around 10^14 passes and 10^41 steps, about three weeks of one core for `prun`. The earlier median (10^53 steps)
came from the ln ln J count.

## The closed pass map

`lean/Pass.lean` leaves out the passes within 6 of the line `r = q`. `lean/Close.lean` (generated by `py/gen_close.py`)
closes the map: for each tag (y, Y), `e = a mod 3`, parity of `j` and `δ = r − q` in 0..6, the pass is again one chain
of zigzags, sweeps and single frames, the same for all sizes, so one theorem each (89 `near_*` theorems; `y` with
`e = 2`, `j` even, `δ ≥ 2` splits off `q = 1` and `q = 1, j = 0`). Exactly five classes do not reach a next zigzag
start, and they are the five halting rows of `lean/Jump.lean`. With the 13 cases of `fast`:

* `cpass` is total on zigzag starts (`cpass_total`) and sound (`cpass_go`: the next zigzag start after that many
  frames of `next`; `cpass_halt`: a halting frame is reached);
* every case maps an even `j` to an even `j`, in a positive number of frames (`cpass_even`);
* on zigzag starts with `j` even it halts exactly on the two rows (`cpass_halt_iff`);
* the run from blank tape reaches its first zigzag start `y(3, 0, 5)` after 6 frames (`first_start`).

So **`halts_iff_row`: the machine halts from blank tape iff the orbit of `y(3, 0, 5)` under the closed pass map
reaches `y(a, j, r)` with `a ≡ 1 (mod 3)`, `r = ⌊a/3⌋ + 2`, or `Y(a, j, r)` with `a ≡ 1 (mod 3)`, `r = ⌊a/3⌋ + 3`.**
This settles the first and third items of the old "Later" list: every halt goes through one of the rows, and only the two
even rows can be met. `orb_frames` runs 10^8 closed passes by `native_decide` (about three minutes) and `no_row`
follows: none of them is on a row.

### Growth runs as one step

A growth pass sends `a = 3q + e` to `4q + c` with `c` fixed by the tag and `e`, so `k` growth passes in a row depend
only on `a mod 3^k`: with `a = 3^k Q + ρ` the end state is `t''(A1 Q + A0, 0, r − (B1 Q + B0))`, the frames are
`F1 Q + F0`, the steps `S2 Q² + S1 Q + S0`, and all `k` passes are growth passes iff `r ≥ G1 Q + G0` (the margin
`r − q − 7` shrinks every pass, so the last one decides). `c/crun.c` builds the tables for `k ≤ 7` at start-up from
the single-pass formulas (exact interpolation in `Q`, checked on a fourth point, at `Q ≈ 10^8` and on both sides of the
condition) and takes each growth run with the deepest table that applies; a drain is one step and the passes near the
boundary go by jumps, as in `prun`. `crun check 20000000000` compares the state, frames and exact steps after every
one of the 8,609,980,394 table steps of the first 2·10^10 passes with the pass-by-pass iteration: no mismatch.
About 8.5·10^7 passes a second, 2.6 times `prun` on the same core (about 2.3 table or drain steps per epoch). A
halt only comes from a near pass, never inside a table, and every start with `|d| ≤ 3` is a drain or a near pass, so
the close calls it prints are complete.

### The run of the closed map

`./crun run 1000000000000000 10000000000 state.txt` (log in `c/run_crun.txt`; it resumes from `state.txt`):

| passes | frames | machine steps | zigzag start |
|---|---|---|---|
| 10,000,000,000 | 38,941,988,752,206,149,446 | 1.1·10^29 | Y(18,669,849,162, 0, 2,099,341,822) |
| 100,000,000,000 | 3,894,236,934,565,580,464,641 | 1.1·10^32 | y(184,676,324,319, 0, 23,016,354,114) |
| 570,000,000,003 | 126,523,705,040,734,829,399,650 | 2.0·10^34 | y(959,814,981,399, 0, 224,031,694,100) |

At 10^10 and 10^11 passes the zigzag start and the frame count are those of `prun` (`c/run_pass.txt`). No halt in
570,000,000,003 passes, 2.0·10^34 machine steps (steps are kept exactly as `hi·2^120 + lo`). Zigzag starts within
2 of a halting row are the ones listed under "The run of the pass map" (the earlier passes agree exactly).

## Halting copies against merging copies (27 November)

The same test as for [1RB1RF_0LC0RF_1RD1LC_---0LE_0RC1LF_1RA0LE](../1RB1RF_0LC0RF_1RD1LC_---0LE_0RC1LF_1RA0LE/README.md)
(its section of the same name has the reasoning). There the count of halting copies was far below the estimate; here
it agreed (311 of 1,000 against about 290), and the exhaustive table says the same thing.

`c/fates.c` follows every zigzag start `y(a, 0, r)` and `Y(a, 0, r)` of level N = a + r ≤ 16,384 with the pass map
(the functions of `c/prun.c`, copied) until it halts or leaves level 16,384: 2.7·10^8 starts in 9 seconds
(`py/fates.py`, `py/fates_run.txt`).

| start levels | starts | halt below 16,384 | orbits the others are on | largest orbit | blank-tape orbit |
|---|---|---|---|---|---|
| 256..287 | 17,120 | 70.1% | 4 | 16.0% | 6.6% |
| 512..575 | 69,056 | 45.3% | 6 | 25.1% | 4.2% |
| 1024..1151 | 277,376 | 27.5% | 10 | 23.4% | 4.2% |
| 2048..2303 | 1,111,808 | 28.4% | 14 | 18.4% | 8.9% |
| 4096..4607 | 4,451,840 | 7.8% | 21 | 11.5% | 7.6% |
| 8192..9215 | 17,816,576 | 3.2% | 47 | 10.6% | 2.3% |

Starts merge as for the other machine (the pass map is two-to-one and a level holds about 2N starts), but less
fast, and the blank-tape orbit is a small one among them: 2 to 9% of the starts join it.

F(L), the fraction of all starts of levels [L/2, L) that halt from a level in [L, 2L):

| L | 2^4 | 2^5 | 2^6 | 2^7 | 2^8 | 2^9 | 2^10 | 2^11 | 2^12 | 2^13 |
|---|---|---|---|---|---|---|---|---|---|---|
| F(L), % | 8.3 | 15.2 | 2.3 | 8.0 | 7.2 | 10.2 | 6.5 | 11.5 | 14.6 | 2.7 |

Mean 8.7% per octave of N. The probe's estimate was 0.045 to 0.060 per doubling of frames, and frames grow like
N², so 9 to 12% per octave. Starts as a whole halt at the estimated rate. The blank-tape orbit has not halted in
570,000,000,003 passes, where about 2.9 halts were expected: one orbit, one trial, about 5%. No predicate was fitted
here: on the other machine none separates the halting tapes from the others, and this map is of the same kind.

## Status

Open. Lean (`lean/Blank.lean`): the halting configurations (`step_none_iff`), no halt in 10,000 steps by the kernel, in 10,000,000 by `native_decide`. C: no halt in 10^9 steps (`tools/c/triage.c`) and in 10^15 steps (`c/mrun.c`, exact macro simulation). Lean (`lean/Phases.lean`, on `lean/Pieces.lean` generated by `py/pieces.py`): the whole frame map, 78 cases over 8 tape shapes, for all sizes (`next_sound`); the undefined cases halt (`none_halts`); the machine halts iff the orbit of `Ph.z 0 0 2` reaches one (`halts_iff`); not in the first 10^8 frames (`no_halt_phases`, `native_decide`; about 4.5*10^11 steps). Lean (`lean/Jump.lean`): whole sweeps and zigzags in closed form (`w_sweep`, `u_sweep`, `y_zigzag`, ...), the jump map (`jump_sound`), five halting rows (`halt_y`, `halt_Y`, `halt_y0`, `halt_y2`, `halt_Y0`), and no halt in the first 146,530,202,670,678 frames (`no_halt_frames`, `native_decide` on 10^8 jumps). C (`c/frun.c`): no halt in 100,000,000,000 jumps, 8.1·10^29 steps. Lean (`lean/Pass.lean`): the pass map, one zigzag start to the next, as 13 affine cases for all sizes (`fast_sound`, `pass_sound`), and no halt in the first 3,893,676,335,181,895 frames (`no_halt_passes`, `native_decide` on 10^8 passes). C (`c/prun.c`): no halt in 1.8·10^11 passes, 6.5·10^32 steps. Lean (`lean/Close.lean`): the closed pass map, 89 more affine cases near the boundary for all sizes, total on zigzag starts, keeps `j` even; the machine halts iff the orbit of `y(3, 0, 5)` reaches `y(a, j, a/3 + 2)` or `Y(a, j, a/3 + 3)` with `a = 1 mod 3` (`halts_iff_row`); none of the first 10^8 closed passes does (`no_row`, `native_decide`). C (`c/crun.c`, growth runs as one step): no halt in 570,000,000,003 passes, 2.0·10^34 steps. Open: whether the orbit ever lands on one of the two rows.

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
python3 holdouts/1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD/py/rules.py                # the rule table and its step counts against direct simulation
python3 holdouts/1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD/py/gen_c.py && git diff --exit-code holdouts/1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD/c/fcases.h
gcc -O2 -o frun holdouts/1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD/c/frun.c && ./frun check 300000 && ./frun rows 60
./frun trace 8000 | python3 holdouts/1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD/py/check_frun.py     # the jumps against the Lean cases
./frun trace 200000 > t.txt && node holdouts/1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD/py/jumps_panel_test.js t.txt  # the page's copy
./frun close 100000000000 1000000000 16      # the long run (c/run_close.txt), about an hour
gcc -O3 -o prun holdouts/1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD/c/prun.c && ./prun check 20000000000   # every fast pass against frun's jumps
python3 holdouts/1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD/py/gen_pass.py ./prun holdouts/1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD/lean/Pass.lean && git diff --exit-code holdouts/1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD/lean
./prun run 300000 1 > p.txt && node holdouts/1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD/py/pass_panel_test.js p.txt   # the page's copy
./prun run 100000000000 0 0 > near.txt && python3 holdouts/1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD/py/near.py near.txt   # c/near_1e11.txt, about 25 minutes
./prun rate 21 500 50000000 100000000      # random orbits (c/rate.txt has the runs used)
./prun run 4000000000000 10000000000 16    # the long run (c/run_pass.txt)
python3 holdouts/1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD/py/gen_close.py ./prun ./crun holdouts/1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD/lean/Close.lean && git diff --exit-code holdouts/1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD/lean
gcc -O3 -march=native -o crun holdouts/1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD/c/crun.c -lm && ./crun check 20000000000   # every table step against the pass-by-pass map
./crun run 1000000000000000 10000000000 state.txt   # the long run of the closed map (c/run_crun.txt); resumes from state.txt
python3 holdouts/1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD/py/page_jumps.py && python3 holdouts/1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD/py/page_pass.py && python3 holdouts/1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD/py/page_close.py && python3 holdouts/build_pages.py 1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD
```

## Later

- Find an invariant of the closed pass map (residues of `a`, `r`, `N`) that keeps the orbit off the two rows; random
  orbits do reach them (`prun rate`).
- Keep `crun` running (the median of the heuristic is around 10^14 passes, 10^41 steps); `state.txt` resumes it.
