# The 4-wall family's far members at 2⁶⁶, pulled back to their loop entries (November 5; untrusted)

This follows step 1 and step 2 of "Next steps" in `../../notes/FOUR_WALL_ORIGIN.md`. Take the far-shape members of the
four- and five-pass routes at 2⁶⁶. Keep those that the count mod 6 allows (W ≡ 2 mod 6, PR #114). Then pull each one
back through the chain's three step maps until the pull-back reaches the loop entry it would need.

**In short.** The pull-back works and is cheap. (Below, an untrusted extra: 95% of the run's entries lie on exact linear relations that none of the roots meets, so the roots can only come from entries in late rounds of a cycle.) Every surviving member maps to one or two explicit loop entries. But it
does not rule the family out. 82 of the 319 four-pass members and 5 of the 19 five-pass members have a root that passes
`EntryFar`. Fourteen of those roots sit inside clusters of the run's own first loop entries above 2⁴⁰ (up to 2,128 of
them within 0.01 in (R/W, (W − b)/W)). Shape cannot separate them. What is left is the same open clean-tape question,
now with one explicit entry for each member.

## Counts

| | n = 4 (Q + 41,943,036 = 2⁶⁶) | n = 5 (Q + 671,088,636 = 2⁶⁶) |
|---|---|---|
| far-shape members, W > 2⁶⁶ (census re-run, same as `far_shape.md`) | 319 | 19 |
| W ≡ 2 (mod 6), the count's condition | 109 | 5 |
| with a `WindowShape` origin (entry, or a landing whose predecessor is a pass start) | 87 | 5 |
| with a root that has `EntryFar` | 82 | 5 |
| with such a root in the run's entry region (R/W ≥ 0.035, (W − b)/W ≥ 0.455) | 53 | 3 |

All 338 members have W ≡ 0 (mod 4), so each one is a possible landing. Their roots split as follows:

- **The member is the loop entry itself** (W ≤ 32R): 73 four-pass and 4 five-pass members. 36 of these entries fail
  `EntryFar` (15W + 26 > 32(W − b + R)). In all, 113 roots pass `EntryFar`.
- **A half pass from an entry** (E = W − 6 ≡ 2 mod 4, R₀ = 2R, E ≤ 32R₀). This is the most common origin: 65 of the
  four-pass members, and 4 of the five-pass ones.
- **A full pass** (E = W − 24, R₀ = 16R, L₀ = 64L₁). Only 2 members, each from an entry, and one of them also from a
  half pass before that.
- **A round-7 landing: never.** For the 77 members with W ≤ 32R the inverse map gives a non-integer R₀. For the rest it
  gives an R₀ that is negative or a predecessor with a gap below 448.

Every pull-back step (70 half passes, 3 full passes) was run forward in the mark model (`haltclasses trace`, first wall
449). Each step lands exactly on the member, with the first wall that `StepWall` predicts, and passes no phase-0 pass
start on the way.

## Against the run's own loop entries

`roots_vs_run.txt` gives, for every root with `EntryFar`, the nearest first loop entry above 2⁴⁰ in the 1/1024 sample
of the blank-tape run (`sample.tsv.gz` in the blank-run project files, 1,536,741 entries). It also gives that entry's
round and how many run entries lie within 0.01. The run's entries are far from uniform: 94% sit near
(R/W, (W − b)/W) = (0.35, 0.85), in round 10. The rest fall in a few dozen tight clusters, one per round of the cycle.
Still, 17 roots (14 members) lie inside a cluster. For example, the four-pass member i = 210,371,200,248 is its own
entry at (0.0667, 0.5641), and 1,071 run entries from round 36 lie within 0.01 of it.

A class of clean tapes that the tree settles gives entries affine in n, so at large width its entries converge to one
point of this plane. A root can only come from a class whose limit point it matches, and then only if the 2-adic class
matches as well. That is the handle of `FOUR_WALL_ALL_N.md`. The next useful computation would be the clusters' limit
points from the clean-tape tree's entry classes, matched against these 113 roots.

## Most of the run's entries lie on exact lines, and no root does

In the 1/1024 sample, the run's loop entries come from a few rounds of their cycle, and in five of those rounds they
satisfy exact integer linear relations (`rel.py`, checked on every entry by `entry_rel.py`):

| round | entries in the sample | relations on (b, W, R) |
|---|---|---|
| 10 | 1,397,978 | 466b − 298W + 635R = 0 and 167W − 1,024b + 2,540 = 0 (one parameter: b, W and R are affine in n) |
| 15 | 43,679 | 56,714b − 39,819W + 89,191R = 0 and 4,855W − 32,768b + 178,382 = 0 (one parameter) |
| 20 | 2,730 | 271,624b − 227,771W + 612,032R = 0 and 16,155W − 65,536b + 153,008 = 0 (one parameter) |
| 17, 18 | 183,330 and 43,691 | 16b − 11W + 24R + 4 = 0 (a plane; W = 2n + 64) |

That is 95.2% of all entries, and 95.2% of those above 2⁴⁰, with no violation. None of the 113 roots satisfies any of
these relations. The closest misses the round-17 plane by 0.013W. So if every entry in those rounds obeys its relation,
which is untrusted and observed only on the sample, the 4-wall members can only come from entries in round 22 or later.
That is the other 4.8% of the run's entries, where the sample shows no linear relation among b, W and R. All 17 roots
that sit inside a cluster of run entries are in such clusters, from rounds 22 to 59. Proving the five relations from the
clean-tape tree's first rounds would make this a theorem. The open part would then be the late-round entries alone.

## Against the clean-tape tree's entry classes: no root is the value of a settled class

`EntryForms.lean` (in `lean/`, untrusted driver) walks `cleanTreeGS 2⁴¹ d` and prints every loop entry it settles,
as affine forms of a, b, c and W in the class's coordinates, together with the class's cone. `match_forms.py` asks
whether a root is the value of some class's (b, c, W) at integer coordinates inside the cone. The first wall is left
free, as it is in the members' families. `calib.py` runs the same matcher on the run's own entries above 2⁴¹ from the
sample, to show that the matcher finds what it should.

| depth d | entry classes | their measure | roots matched (of 113) | run entries matched (of the first 3,000 above 2⁴¹) |
|---|---|---|---|---|
| 30 | 2,880 | 0.0013395 | 0 | 2,935 |
| 36 | 28,660 | 0.0013412 | 0 | 2,942 |
| 40 | 169,631 | 0.0013416 | 0 | 2,942 |

So 98% of the run's actual entries are values of classes settled by depth 36, but none of the roots is. A halting
member of the 4-wall family at 2⁶⁶ could therefore only be entered from a clean tape that the tree leaves unsettled
at depth 40, or from one of the roughly 2% of entries that the matcher misses. This is what the 2-adic picture of
`FOUR_WALL_ALL_N.md` predicts, and it is no proof. Still, it is the first direct check of the far members' entries
against the tree's classes. Run from `lean/` after `check_end.sh`:
`lean --load-dynlib=cbuild/so/libBB6all.so --run EntryForms.lean 2199023255552 40 > ef40.txt` (about 25 minutes,
25 MB), then `python3 match_forms.py ef40.txt`.

## Files

- `pullback.py`: the inverse of `StepMap` and `StepWall` (`lean/BB6/Ends.lean`) for the full pass, the half pass and
  the round-7 break, and `WindowShape`.
- `dump.py out name R1 R2 C c j Wexp`: every far member from the census outputs of `far_route.py`
  (`tools/routes/far/loop/` in the halting-classes project files; set `FARLOOP` to that folder for `smallmod.py`).
  The outputs are `n4.tsv` and `n5.tsv`: route, i, R, b, W, R/W, (W − b)/W, W mod 6, W mod 4, shapes.
- `classify.py`: the origins of each W ≡ 2 (mod 6) member (`n4.cls`, `n5.cls`).
- `verify.py n5.cls n4.cls`: the forward check of every pull-back step (set `HALTCLASSES` to the native binary that
  `build.sh` there makes).
- `survive.py`: the table above (`survive.txt`).
- `near.py entries.txt`: the roots against the run's entries (`roots_vs_run.txt`). `entries.txt` holds R/W,
  (W − b)/W, W mod 4 and the round for each `E` row of `sample.tsv.gz` with W > 2⁴⁰.
- `census_hi45.txt`: `far_route.py routes_hi45.txt 3 66` with `FIXBITS=32`, rebuilt from scratch. It reproduces the
  319 and 19 members of `far_shape.md`.
- `rel.py`, `entry_rel.py entries_all.txt`: the integer relations of the run's entries per round (`rel_out.txt`) and
  their check on every entry, with the roots against them (`entry_rel.txt`). `entries_all.txt` holds n, round, b, W and R
  for each `E` row of `sample.tsv.gz`.
- `match_forms.py forms.txt`, `calib.py forms.txt entries_all.txt [limit]`: the roots, and the run's own entries,
  against the entry classes that `EntryForms.lean` prints.
