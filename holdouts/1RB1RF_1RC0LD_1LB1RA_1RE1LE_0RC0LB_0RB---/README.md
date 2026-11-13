# 1RB1RF_1RC0LD_1LB1RA_1RE1LE_0RC0LB_0RB---

bbchallenge id 65352. A BB(6) holdout, group G10 (one side of the tape grows like the square root of the step count, the other more slowly). Analysed by hand from the generated folder.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RF |
| B | 1RC | 0LD |
| C | 1LB | 1RA |
| D | 1RE | 1LE |
| E | 0RC | 0LB |
| F | 0RB | --- |

## What it does

**The tape is a run of 1s written in two encodings.** A sweep to the right turns each triple `100` (or `001`, `010`,
by its phase) into `111`; a sweep to the left turns `111` back into `001` (or `100`, `010`). Read at the right end,
the tape is a few blocks of 1s separated by single 0s.

**A marker zig-zags to the end.** Most of the time the head bounces between the right end and one 0, the marker.
Read at the right-end turns:

```
step 1,220,413   1 0 1^1678 0 1^9 B>1 1
step 1,220,437   1 0 1^1682 0 1^5 D>1 0
step 1,220,455   1 0 1^1686 0 1^3 B>1 1
step 1,220,467   1 0 1^1690 D>0 0          the marker has reached the end
```

As a rule on the gap g from the marker to the head:

```
X 0 1^g B>1 1   ->   X 1^4 0 1^(g-4) D>1 0
X 0 1^g D>1 0   ->   X 1^4 0 1^(g-2) B>1 1
```

The marker gains 3 cells on the end per bounce, and the end moves 1 cell per bounce.

**Each pass multiplies the width by about 4/3.** A marker launched g cells from the end catches it after about g/3
bounces, by which time the end has moved g/3 cells: the pass ends with the tape g/3 cells wider (checked on every
single-marker pass to 1.6·10^10 steps, up to a few cells). New markers start near the left end, so g ≈ W and
W → ≈ 4W/3. Widths at the ends of passes: 706, 945, 1266, 1694, 2258, 2993, 3971, 5301, 7069, 9410, 12506, 16503,
21553, 28137, 36714, 47058, 60838, 81101, 108115, 144158, 192218. Steps grow like 0.42·W², so the right side grows
like sqrt(steps) and the number of passes like log(steps).

**A prefix at the left end decides the next marker.** When a marker arrives, the head sweeps to the left end, changes
a few cells and launches the next marker. The cells left of it form a short prefix with few shapes (`1 0`,
`1 0 1^39 0`, `1^73 0`, `1^73 0 1^2355 0`, ...); sometimes an old marker stays behind and the next pass starts
further right, giving W' = (4W − P)/3 with P the prefix length. The shape depends on W mod 3, since the leftward sweep
converts in triples counted from the right end.

## Halting

The only halting transition is F1, reached as `A>1 1` (A reads 1, F reads the next cell, also 1). In a sweep in the
expected phase A always meets a 0 there; halting needs a rightward sweep to meet triples out of phase. The pass map
is Collatz-like (×4/3 with a residue-dependent correction and a finite-state prefix), and whether its residues ever
produce the mismatch is open.

## What is proved

- `lean/Blank.lean` (generated): the halting configurations; no halt in 10^4 steps (kernel) and 10^7 (`native_decide`).
- `lean/Rules.lean` (from `py/rules.py`, kernel): the six shift rules of the two sweeps, and the D-type bounce of the
  zig-zag, `L 0 1 1 (111)^(m+1) D>1 0^∞ → L 1111 0 11 (111)^m 1 B>1 1 0^∞`, for every m and L.
- `lean/Pass.lean` (pieces from `py/pass.py`, induction by hand, kernel): the whole zig-zag of a marker, for every gap
  and every tape left of the marker. Written with the head in B on the last 1 of the tape (`L` is the tape left of the
  marker, `w8` = `1^8`):
  - `z_two`: `L 0 (111)^(m+2) B>1 0^∞ → L 1^8 0 (111)^m B>1 0^∞` (two bounces: the marker moves 8 cells, the gap
    drops by 6, the tape grows by 2);
  - `z_pass j`: by induction, `L 0 (111)^(m+2j) B>1 0^∞ → L 1^(8j) 0 (111)^m B>1 0^∞`;
  - `pass_c e j L`: a marker launched with gap `3(e+2j+1)+1` (head in C just right of the end) runs to
    `L 1^4 1^(8j) 0 (111)^e B>1 0^∞`;
  - `pass_l0 e j`, `pass_l2 e j`: the launch from the left end with no marker and width `3(e+2j+3)` or `3(e+2j+3)+2`,
    run to the same form with the prefix `1 0 1 1` or `1 0 1^6`.

  So the zig-zag part of a pass is exact: gap `3(e+2j+1)+1` goes to `3e`, the tape grows by `2j` cells. The end of
  the pass (gap below 6, the head turning into the left sweep), the left-end turn with a prefix, and launches with a
  marker at gap ≡ 0 or 2 (mod 3) are not proved: there the symbolic run reaches the cells left of the marker, so each
  case depends on the prefix.
- Computed (`c/passes.c`): no halt in 2·10^10 steps.

Heuristic: the end of a pass and the left-end turn, the 4/3 law, the prefix shapes.

## For later

- Prove the end of a pass for each residue of the final gap, and the launches with a marker for gap ≡ 0, 2 (mod 3)
  for each prefix shape (`py/pass.py` gives `TouchContext` for these: the head reaches the prefix).
- Write the left-end turn for each prefix shape and each residue of W mod 3, and so the exact pass map
  (W, prefix) → (W', prefix'). Iterating that map (in Python, exactly) would reach far beyond 10^10 steps and would
  say whether the residues are equidistributed; a closed finite set of (prefix, residue) cases with no halting
  case would prove nonhalting, a halting case reachable from the run would give the halt.
- Compare with the bbchallenge "4/3" Cryptids (Antihydra is a 3/2 map of the same kind).

## Reproduce

```sh
python3 holdouts/1RB1RF_1RC0LD_1LB1RA_1RE1LE_0RC0LB_0RB---/py/rules.py > /tmp/R.lean   # = lean/Rules.lean
(cd holdouts/1RB1RF_1RC0LD_1LB1RA_1RE1LE_0RC0LB_0RB--- && python3 py/pass.py) > /tmp/P.lean   # pieces of lean/Pass.lean
gcc -O2 -o passes holdouts/1RB1RF_1RC0LD_1LB1RA_1RE1LE_0RC0LB_0RB---/c/passes.c
./passes 20000000000            # every launch of a marker: width, gap, prefix (about 4 minutes)
```

## Pages

- [`pages/holdouts/1RB1RF_1RC0LD_1LB1RA_1RE1LE_0RC0LB_0RB---/explainer.html`](../../pages/holdouts/1RB1RF_1RC0LD_1LB1RA_1RE1LE_0RC0LB_0RB---/explainer.html)
- [`pages/holdouts/1RB1RF_1RC0LD_1LB1RA_1RE1LE_0RC0LB_0RB---/proof-status.html`](../../pages/holdouts/1RB1RF_1RC0LD_1LB1RA_1RE1LE_0RC0LB_0RB---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RF_1RC0LD_1LB1RA_1RE1LE_0RC0LB_0RB---/lean/check.sh
```
