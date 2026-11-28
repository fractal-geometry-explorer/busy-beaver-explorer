# What busycoq's maintainer changed when merging 40 pull requests (27 November 2026)

On 27 November 2026 busycoq's maintainer (ccz181078) merged 40 more pull requests into the BB6 branch, which now
stands at `70a1ffc`. They are #47, #54, #56, #58, #61 to #63, #65, #69 to #80, #83 to #85, #87 to #89, #91, #93 to
#96, #104, #105, #107, #111 and #115 to #119. Nine of them (#69 to #77) are this project's own Coq proofs.

**No verdict changes.** The merged pull requests cover 46 holdouts, and all 46 were already decided here, either by
a proof in this repository or by an outside proof compiled here. One more pull request, #77, proves that
1RB---_1LC0RF_1LD0LC_0RE0LF_0RD1LA_1RB0LE halts exactly when 1RB0RA_0LC0RF_0LB1RD_1LE---_1RA0LF_1LE0RC does. That
settles neither machine. #65 gives time bounds for the BB(6) champion and is not about a holdout. The index still
counts 506 undecided holdouts. 84 holdouts are now proved in busycoq's BB6 branch.
`holdouts/external.json` records each merge (merge commit, the files that now hold the proof, whether the maintainer
rewrote it), and the 48 affected machines' pages were rebuilt.

**Most proofs were rewritten before merging.** Only #61 to #63 went in unchanged. For every other pull request the
maintainer pushed a follow-up commit. The pull requests added about 241,000 lines in total; the merged result is
about 116,000 lines. The rewritten versions were not recompiled here (the `compiled` entries in `external.json` are
the pull requests' own versions). Many rewrites switch from `vm_cast_no_check` to `native_cast_no_check`, which also
trusts Coq's native compiler. That is busycoq's usual practice, and `external.json` marks these proofs with
`"native": true`.

The rest of this note is what the rewrites teach, then what that means for open holdouts.

## 1. Seven patterns in the rewrites

The seven commits the user pointed to are the rewrites of our own pull requests (#69 to #77). Each pattern below
lists those commits first, then other pull requests where the maintainer did the same thing.

### a. Share one check between machines that are the same table (ae8a970, #69 and #70)

#69 and #70 are one table started in two states. Our submission checked the same 62-tape certificate twice, once per
file. The merged version keeps one closure check in `PR69Shared.v` and adds a 60-line `PR70Mapped.v`. That file
renames states (`rename : Q -> Q`), proves that the renaming maps each step of one machine to a step of the other
(`map_step`, `map_halts`), and reuses `PR69Shared.template_nonhalt`. The expensive computation now runs once.

The same pattern elsewhere:
- #93: the two machines are now 18-line files over `PR93PairEngine.v`, using `Perm (flip (src_tm b)) tm rename93`.
- #84: one shared accelerator for two machines.
- #78/#79: a shared base dispatcher.
- #96/#104: a shared 16-phase closure.
- #115 to #119: one return dispatcher for five machines (`PR115_119Dispatch.v`, which replaced 32,444 lines).
- #54: one wave proof for the four collar machines (22,168 lines deleted).

### b. Put the differing transitions behind a parameter (a63242f, #72 and #73)

#72 and #73 differ in one transition, E1. Our two files repeated every lemma. The merged `PR72_73Visit.v` defines
`machine (e1 : option (Sym * dir * Q))` and adds one reconvergence lemma, `e_common`. That lemma shows that after
E1, both variants reach the same configuration (`l E> 1 0 r -->+ 0 1 l C> r`). Every other lemma is then proved once,
inside a `Section` over the flag. `PR93PairEngine.v` does the same thing for #93: two cells sit behind
`variant489 : bool`, and the comment says "every symbolic macro below has the same meaning for both machines; the raw
fallback consults the flag".

### c. Compute certificates in the prover; don't store them (782fe4e #77, 715497b #74, 808e238 #75)

- #77: our file listed the 28 abstract configurations of the invariant by hand. The merged file finds them with a
  bounded worklist search, `discover 128 [abs cfg0] []`, run by `Eval vm_compute`. The search is not trusted: the
  closure check `check_S0` is what proves the result. The abstract step is no longer written by hand either. It is
  the concrete step run on one representative per case (`representatives`, `representatives_cover`), so the hand
  case analysis of `anext_spec` disappears.
- #75: the batch step simulated the tail twice, once to count and once to advance. Now `regular` returns both the
  count and the endpoint, and the proof uses them.
- #74: the block cache moved from `PositiveMap` to a direct-mapped `PArray` of 2^20 slots keyed by packed
  `Uint63` blocks. An index collision can only evict an entry, never certify a wrong one, because the exact tag and
  block are compared on every lookup.

The same pattern elsewhere. Each item is the rewrite commit's own title:
- #83: "discover and check symbolic jumps rather than storing a replay" (4,110 lines deleted).
- #88: "compute bounded recursive returns without a precomputed DAG" (18,982 lines deleted).
- #91: "generate and verify the edge-closure stages" (7,242 lines deleted).
- #89: "discover and check the waves without a stored replay" (6,770 lines deleted).
- #85, #87: the cycle seed and the loop seed are computed instead of stored.
- #94: checkpoint lookups are computed instead of stored as index hints.

### d. One lemma for both directions (a0c89f6, #71)

Our #71 had `OKR`/`OKL`, `chkR`/`chkL`, `cross_r`/`cross_l` and `crossWith_R`/`crossWith_L`: four mirrored pairs.
The merged file introduces `orient d near far`, so that a crossing is stated in (near, far) coordinates. Each pair
then becomes one lemma over `d : dir`. #77 does the same with `orient b q l a r` for its two machines. The rewrite
also deleted a strategy (`stratLin`) that the final proof never used.

### e. Check the round trip, not each field (964ce4e, #76)

Our `tryJump` checked five decoded fields one by one with `andb`, which evaluates all of them every time. The merged
version tests the cheap guards first in a chain of `if`s. It then checks only that re-encoding the parsed zone gives
back the input (`items_eqb (encZone ...) b`), which makes `lv_eqb` and its lemma unnecessary. The round results now
go through one soundness predicate and a bind (`sound`, `rr_bind`), so `round_next`, `round_halt` and `seq_sound`
become `round_sound` plus `rr_bind_sound`.

### f. Keep the expensive check apart from the library (a63242f)

`VisitLaw2.v` no longer runs `check_ok`. The 161,210-round run is a single lemma in `PR72_73Check.v`, so the library
and the soundness theorem build without running it ("the soundness theorem and the physical visit laws can be built
without running this check").

### g. Use the library's lemmas

#74's hand inductions for `sweep1` and `rotate` were replaced by the library's `shift_rule_R` and `lpow_rotate'`.
#75 uses `List.rev'` and `fold_right` in place of `rev` followed by `fold_left`.

## 2. What this means for our own submissions

Our three busycoq pull requests still open are #108, #109 and #120. #102 is valu42's.

- **#100, #102 and #108 are one table started in three states.** Up to renaming and mirroring, all three are
  1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0LC--- (`related.json`). That table is the source table of `PR93PairEngine`
  with one cell changed, F0 = 0LC instead of 0RD. #100 was merged on 26 November as a 5,742-line copy of the PR 93
  engine. #102 and #108 are 5,734- and 5,730-line copies of the same engine, and both are still open. Pattern (b)
  says what to do: put F0 behind the engine's flag as a third variant. The three proofs then become `checker variant
  k q` calls, `q` being the start state, which the checker already takes. That replaces about 11,500 open lines with
  about 60. #109 (1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB0LE) differs from the same source table in two cells, so it
  might fit as a fourth variant.
- **#120** stores 400 checked segments. Pattern (c) suggests generating them inside Coq and checking them there.
- **For future pull requests:**
  - write one proof per family, with the differing cells as parameters;
  - add a renaming lemma for start twins;
  - let a search produce certificates, then check them, instead of storing them;
  - state shift rules once with a direction parameter;
  - put the one heavy evaluation in its own file.

  These are the changes the maintainer makes anyway. Doing them first means less rewriting on their side.

## 3. Can the same methods settle open holdouts?

The rewrites change how proofs are written, not which machines can be proved. Patterns (a) and (b) only pay off once
one member of a family is decided. So the useful check is for open holdouts that are a renaming, a start twin, or a
one-cell variant of a decided table.

**Screen (27 November 2026).** `tools/deepmind/neighbours/screen.py` was run with all 101 tables decided here
(`decision` not open) against the 507 holdouts whose decision is open. It matched 12 tables, which are 11 holdouts
(one matches two ways). None of the matches is new:
- **The start twin of #76.** 1RB0LC_1LC0RE_1LD1LB_1LA1LD_1RF0RA_---1RE is the halting table
  1RB1RD_1RC1RB_1LD0RA_1RA0LE_1LF0LC_---1LE started in C and mirrored. This was already in `related.json`, where the
  two runs share no configuration. A renaming lemma like #70's would transfer a closure check, but the #76 proof is
  a run from blank tape with jumps, not a closure check. A start twin needs its own run, so nothing carries over.
- **Ten holdouts in the vampire family.** They are variants of our own #109 table (F1 replaced by 0LF, 1LF or 1RE,
  with other starts). These are already studied in `bb6-vampire-family/`. The proved theorem there reduces halting
  to a map of (context, n), and no closure exists for that map.

The earlier screen of 236,071 proved tables
([`followup/invariant-transfer.md`](followup/invariant-transfer.md)) already covered lockstep re-sync with
neighbours, so it was not repeated.

**Where the pattern can still help.** Some open families share one question:
- the F05 twins and start twins ([`../EQUIVALENCES.md`](../EQUIVALENCES.md));
- the #77 pair;
- the seven vampire-family machines.

For each of these, a future proof should be written once, with the differing cells as a parameter as in (b), and a
renaming lemma as in (a). It would then settle the whole family at once. Pattern (c), discovering an abstract
invariant by search and checking that it is closed (with the abstract step taken from the concrete step on
representatives), is a reusable decider skeleton. It is the shape that the closed-set and window screens in
`followup/` already use outside Coq. Porting those screens' certificates to Coq in this form is the cheapest way to
turn any future screen hit into a proof that can be merged.
