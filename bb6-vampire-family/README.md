# The vampire family: seven holdouts, one map

Seven machines of the list of 608 BB(6) holdouts are, after renaming their states (and, for one of them, mirroring
the tape), one core table with a single entry varied:

```
A 1RB0LA   B 0RC0RB   C 1LD1LA   D 1LC1RE   E 1RF0RD   F ??? ---
```

with F0 one of `1LC`, `1LA`, `1RB` and the run started in A, E or F. Thomas Reus's repository
[bb6-vampire-family-1RB0LA_0RC0RB_1LD1LA_1LC1RE_1RF0RD_1LC---](https://github.com/thomasreus-bb/bb6-vampire-family-1RB0LA_0RC0RB_1LD1LA_1LC1RE_1RF0RD_1LC---)
studies this family (it calls the runs "Bells" and the four distinct runs orbits O1 to O4). This folder proves in
Lean, on the shared library [`tools/lean`](../tools/lean/), that each machine's halting question **is** a question
about an explicit map on (context, n), and evaluates that map for 2^18 passes. It does not settle any of the seven.

| Machine | Core variant | Start | First E-event (step, context, n) |
|---|---|---|---|
| `1RB---_1LC0RB_0LD0LC_1RE1RB_1RD1LF_1LA0LE` | F0 = 1LA | F (tape mirrored) | 105, `1`, 15 |
| `1RB0RF_1LC---_1RD0LC_0RE0RD_1LF1LC_1LE1RA` | F0 = 1LA | E | 80, `10001`, 9 |
| `1RB0LA_0RC0RB_1LD1LA_1LC1RE_1RF0RD_1LC---` | F0 = 1LC | A | 153, `1`, 19 |
| `1RB0RE_1RC---_0RD0RC_1LE1LF_1LD1RA_1RC0LF` | F0 = 1RB | E | 114, `1`, 17 |
| `1RB0LA_0RC0RB_1LD1LA_1LC1RE_1RF0RD_1LA---` | F0 = 1LA | A | 123, `11`, 15 |
| `1RB---_0RC0RB_1LD1LE_1LC1RF_1RB0LE_1RA0RD` | F0 = 1RB | F | 139, `11`, 17 |
| `1RB0RF_1LC---_1LF1LD_1RE0LD_0RC0RE_1LC1RA` | F0 = 1LC | E | 27, `1`, 7 |

The renamings: `python3 py/family.py match`. The first events: `python3 py/family.py first`.

## The map

An **E-event** is the configuration `c E> 1^n` with only blanks beyond the block, entered by D1 → 1RE (not right
after E1 → 0RD). The word `c` is the tape from its first 1 to the head: the **context**. From an E-event:

1. **The E-pass** (the only part that reads F0) halves the block: it ends in `Cq c q m`, the head in C on the first cell
   of a block of m ones, with m = 2u + 2 + 3q and q = n/2 − 1 + e (n even) or q = (n − 3)/2 + f (n odd), and
   b = q mod 2:

   | F0 | e | u | f | v |
   |---|---|---|---|---|
   | 1LC | 1 | 0 | 0 | 3 |
   | 1LA | 0 | 1 | 1 | 1 |
   | 1RB | 0 | 2 | 1 | 2 |

   (the block left behind is 2u + 2 cells for n even, 2v + 2 for n odd).
2. **The context rewrite** then depends only on (c, b): it either halts, or reaches the next E-event `c' E> 1^(m+a)`,
   with c' and a fixed by (c, b). It never reads F0, so it is the same for the three variants.

So the run from blank tape is: a few hundred steps to the first E-event, then iterating
(c, n) ↦ (c', m(n) + a(c, b)) until some (c, b) halts. Each iteration multiplies n by about 3/2.

## What is established

**Proved in Lean, kernel only** (`Core/`, `VLC/`, `VLA/`, `VRB/`, and the first five theorems of each
`Machines/H<id>.lean`):

- `Core.drain`: the drain of the halved block, for every F0 (`Core.trans f0` with `f0` a variable).
- `Core.tbl_sound`: the rewrite of each of the **99 contexts** of the table (both values of b), for every F0. A
  table entry is either the next context and offset, or "halts"; the halting entries are proved to halt.
- `V*.pass`, `V*.nextE_sound`, `V*.haltE_sound`: for each variant, an E-event with n ≥ 6 reaches the next one
  computed by `nextE` (when its context is in the table), or halts when `haltE` says so.
- `V*.orbit_sound`, `V*.check_sound`: iterating `nextE` K times (`oiter`) is sound, and `check K` returning true
  means the machine halts.
- For each machine: `halts_iff` (the machine halts from blank tape iff the core variant halts from blank tape in the
  start state above, by renaming, or renaming and mirroring, with `TM.halts_of_map`), `x0_reaches` (the first
  E-event, checked by `decide +kernel`), and the two criteria:
  - `halts_of_check K : V.check K x0 = true → HaltsFromBlank`
  - `not_halts_of_forall : (∀ K, (V.oiter K x0).isSome) → ¬ HaltsFromBlank`
  - `orbit_kernel`: the first 10,000 passes stay in the table without a halt (`decide +kernel`).

**Proved with `native_decide`** (trusts the compiler): `orbit_native`, 2^18 passes, all in the table and none
halting; `no_halt_native`, so the machine runs more than 10^45000 steps.

**Checked by computation, not proved:**

- The map agrees with direct simulation of each machine for its first 14 E-events (`python3 py/family.py check`).
- [`c/orbit.c`](c/orbit.c) (iterates the map 2-adically, from the holdout folder's `orbit.c`) agrees with the
  outside repository's checkpoints at its Bell 1,000,001 on all four orbits, and with an independent checkpoint of
  orbit O2 at Bell 3.5·10^9.
- The seven machines fall on four orbits, as the outside repository says: over passes 10 to 50, the runs of
  `1RB0RF_1LC---_1RD0LC_0RE0RD_1LF1LC_1LE1RA`, `1RB0LA_0RC0RB_1LD1LA_1LC1RE_1RF0RD_1LC---` and
  `1RB0RE_1RC---_0RD0RC_1LE1LF_1LD1RA_1RC0LF` meet the same contexts with n differing by 2 (one pass apart for the
  first two), and so do `1RB---_0RC0RB_1LD1LE_1LC1RF_1RB0LE_1RA0RD` and `1RB0RF_1LC---_1LF1LD_1RE0LD_0RC0RE_1LC1RA`.
- The table: the contexts used by the seven orbits in their first 2^30 passes, plus every context of weight at
  least 10^-13 within 300 passes of a Markov model with fair bits (the halting rate of that model is
  8.9·10^-13 per pass; its main halting entries are in the table). [`py/contexts.txt`](py/contexts.txt).

**Reported by the outside repository, not reproduced here:** all seven halt. Its program `belldco` found a halt on
each orbit: O1 (`1RB---_1LC0RB_0LD0LC_1RE1RB_1RD1LF_1LA0LE`) at Bell 747,242,483,684; O2
(`1RB0LA_0RC0RB_1LD1LA_1LC1RE_1RF0RD_1LC---`, `1RB0RF_1LC---_1RD0LC_0RE0RD_1LF1LC_1LE1RA`,
`1RB0RE_1RC---_0RD0RC_1LE1LF_1LD1RA_1RC0LF`) at Bell 731,899,010,932, found on two computers; O3
(`1RB0LA_0RC0RB_1LD1LA_1LC1RE_1RF0RD_1LA---`) at Bell 1,961,935,897,288; O4
(`1RB---_0RC0RB_1LD1LE_1LC1RF_1RB0LE_1RA0RD`, `1RB0RF_1LC---_1LF1LD_1RE0LD_0RC0RE_1LC1RA`) at Bell
1,941,376,761,248. Those are about 10^(2.6·10^11) to 10^(6.9·10^11) steps.

## What remains

With the reduction proved, a halting proof of any one machine is `halts_of_check K` with `V.check K x0 = true`
evaluated, where K is the halting pass. Two things are missing:

1. **The contexts.** The table must contain every context the orbit visits up to its halt. It has those of the
   first 2^30 passes; the halting pass is near 7·10^11 to 2·10^12. The outside repository's halting words suggest
   the halting entry is among the table's, but the contexts between 2^30 and the halt have not been listed. Running
   `c/orbit.c` to the halt with context counting would list them (one more run per orbit, of the size of the
   outside repository's), then `py/contexts.py` and `py/gen.py` regenerate the table.
2. **The evaluation.** At the halt n has 2.7·10^11 to 7.3·10^11 bits, so `check` on plain `Nat` cannot reach it
   (GMP, under Lean's `Nat`, caps one number at about 1.37·10^11 bits, and 10^12 passes one by one are far too
   slow). The **2-adic checker** below does it: written in Lean, proved sound, checked against `c/orbit.c`. What is
   left is to run it once, with `native_decide`, on a machine with a few hundred GB of memory.

## The 2-adic checker (`lean/Adic/`)

The map is (c, n) ↦ (c', (3n + d)/2) with c' and d fixed by c and n mod 4. So k passes depend only on
n mod 2^(k+1), and 2^k n_k = 3^k n + B_k with B_k a function of c and n mod 2^(k+1). The checker computes
(c_k, B_k) by divide and conquer, the method of `c/orbit.c`:

- `Adic.solve` does k/2 passes from the low k/2 + 1 bits, then the low k − k/2 + 1 bits of n_(k/2) from those, then
  the other half. The leaves (`Adic.leaf`) do up to `Lf` passes one at a time on small numbers.
- `Adic.seg` strings segments of L passes together on the full n. It keeps n as a list of L-bit digits, so no single
  number is longer than about 2.6·L bits. With L = 2^35 every number stays under GMP's cap, and n can be as long as
  memory allows.
- The table is `Core.tbl` numbered (`Adic.mkTab`): entry 4c + r is the next context number and d for n mod 4 = r, or
  "halts", or "outside the table".

**Proved in Lean, kernel only** (no `native_decide`; axioms `propext`, `Classical.choice`, `Quot.sound`):

- `Adic.leaf_sound`, `Adic.solve_sound`: for every n with the given low bits, a result `go c' B` is what k passes of
  the abstract map give, with 2^k n_k = 3^k n + B. A result `halt` means the orbit meets a halting entry within k
  passes.
- `Adic.seg_sound`: `seg … = true` means the orbit of (c, val ds) meets a halting entry.
- `Adic.halts_of_meets`, `Adic.halts_of_seg` (`Adic/Link.lean`): the abstract orbit is the orbit of `nextE`, and a
  halting entry is a halt of the machine. They use two facts about each variant's E-pass, `V*.Adic.nextOK` and
  `V*.Adic.haltOK` (`Adic/V*.lean`, which restate `V*.nextE_sound` and `V*.haltE_sound`, with omega).
- For each of the seven machines, `H<id>.halts_of_seg` (`Adic/Machines.lean`): if `Adic.seg V.Adic.tab L Lf f (3^L)
  s i [n]` returns true from the machine's first E-event, the machine halts from blank tape.
- `Adic.Test.halt_example`: the whole chain on a real halting E-event, evaluated by the kernel. From context 43 of
  the table with n = 13,913, the core with F0 = 1LC meets a halting entry at pass 20. The checker finds it, so that
  configuration halts.

**Checked** (`Adic/Test.lean`, `native_decide`): over 4,096 passes from the starts of the three variants, `solve`,
the abstract map and the existing `V*.oiter` agree on every context and n, and 2^k n_k = 3^k n + B_k holds.

**Checked by computation, not proved:** compiled, the checker gives the same n_K mod 2^64, bit length and final
context as `c/orbit.c` on `1RB0LA_0RC0RB_1LD1LA_1LC1RE_1RF0RD_1LC---` after 2^14, 2^20, 2^24 and 2^28 passes, with one
segment or several, and on `1RB0LA_0RC0RB_1LD1LA_1LC1RE_1RF0RD_1LA---` after 2^20 passes (`lean/Adic/bench/`). It takes about 1.4 times as long as `c/orbit.c`: 2^28 passes in 61 s (4 segments of 2^26 passes,
leaves of 24) against 42 s.

### What the final run needs

1. A table with every context of the orbit up to the halt (the run of item 1 above, then `py/contexts.py`,
   `py/gen.py`, `py/gen_adic.py`). The current table holds the first 2^30 passes, and the checker reports
   `out` (no proof) if the orbit leaves it.
2. One evaluation per orbit, for example for `1RB0LA_0RC0RB_1LD1LA_1LC1RE_1RF0RD_1LC---` (orbit O2):

   ```lean
   theorem halts : H121010.HaltsFromBlank :=
     H121010.halts_of_seg (2 ^ 35) 24 64 22 (by decide) (by native_decide)
   ```

   with 22 segments of 2^35 passes covering the reported halting pass, about 7.3·10^11. Checked with
   `tools/lean/check_native.sh`, so that the evaluation runs compiled code.
3. A large machine. Scaling the 2^28 timing by K log² K gives very roughly 4 days for O1 and O2 and 10 to 12 days
   for O3 and O4, on one core (GMP under Lean is single-threaded). That is an extrapolation, not a measurement. The
   state n alone is 34 to 91 GB at the halt, and the products of a 2^35-pass segment need tens of GB more, so
   256 GB of memory is the safe size.

## Files

- [`py/family.py`](py/family.py): the core, the renaming of each machine onto it, the simulator, the E-event map.
- [`py/contexts.py`](py/contexts.py): chooses the table's contexts (writes [`py/contexts.txt`](py/contexts.txt)).
- [`py/gen.py`](py/gen.py): writes every Lean file (symbolic proofs from `tools/py/bbtools/symtm`).
- [`c/orbit.c`](c/orbit.c): the fast orbit, for any member of the family.
- [`py/gen_adic.py`](py/gen_adic.py): writes `lean/Adic/V*.lean` and `lean/Adic/Machines.lean`.
- `lean/Adic/`: the 2-adic checker (Basic: the checker and its soundness; Link: the table and the tie to the
  machines; V*: each variant's E-pass in the checker's form; Machines: the seven halting criteria; Test).
- `lean/Core/` (Machine, Rules, Defs, Ctx), `lean/VLC/`, `lean/VLA/`, `lean/VRB/` (Machine, Rules, Map),
  `lean/Machines/H<bbchallenge id>.lean` (21328, 119593, 121010, 92948, 160156, 82614, 134470, in the order of the
  table above).

## Reproducing

```sh
. /etc/profile.d/lean.sh
bb6-vampire-family/lean/check.sh          # every file, the checker included, about 6 minutes from scratch
python3 bb6-vampire-family/py/gen.py      # regenerate the Lean files (from py/contexts.txt)
python3 bb6-vampire-family/py/family.py check
bb6-vampire-family/lean/Adic/bench/build.sh    # the compiled checker, after check.sh
bb6-vampire-family/lean/out/bench/bench LC 0 19 65536 16   # 2^20 passes; compare ./orbit 0 check 1048576
cd bb6-vampire-family/c && gcc -O2 -o orbit orbit.c -l:libgmp.so.10
./orbit 20                                # 2^20 passes of 1RB0LA_0RC0RB_1LD1LA_1LC1RE_1RF0RD_1LC---, context counts
MACH=1RB0LA_0RC0RB_1LD1LA_1LC1RE_1RF0RD_1LA--- C0=11 N0=15 ./orbit 20
python3 bb6-vampire-family/py/contexts.py 300 orbit-run-*.out   # the outputs of the seven runs
```
