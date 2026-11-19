# token-sims: PRs 85, 87, 90, 94, 96, 104 (Alex Havrilla, DeepMind)

All six: one Rocq file importing only busycoq `Individual62`, no axioms (`Print Assumptions` closed), certificates
discharged by `vm_cast_no_check (eq_refl true)`. Common shape: a verified symbolic/RLE executor
(`exec_sound : run s = Some s' -> decode s -[tm]->* decode s'`) + one or two `vm_compute` certificates + a
closure lemma (`progress_nonhalt_simple/cond` for nonhalt, `halted` config for halt).

## PR 85 / PR 87: parametric crystal + opaque word attractor (`Chunk`/`RState`/`stepFast`/`ActRepack`)
- Tape = list of `Chunk`s: raw bits `b0/b1`; `pL r`/`pR r` = c copies of a fixed period-66 word (rotation r), c a
  global parameter; `wL f`/`wR f` = a global bit list w (or its complement if f) in 4-cell letters (1000/0100 outward).
  87 adds RLE quadruplet runs (`rL0100 n` ...) and compact deques (`swL`, `bzL`) for long fixed raw stretches.
- `decode w c s`: every crystal chunk shares c, every word chunk shares w. Crossing lemmas are proved by induction for
  arbitrary w and arbitrary c (11 base micro-steps lifted to sweeps), so `stepFast` is sound for all (w, c) at once.
- Hub (85): A at right end on blank, left = 115 raw | P66^c | 1,746 raw | enc(w) | 268 raw. Cycle: 1 raw step, 81,201
  `stepFast` steps, one `ActRepack` (pure list algebra: `repack_wp_gen`) to decode (u_top ++ w^(f) ++ u_bot) (c+2)
  hub, |u_top| = 42, |u_bot| = 270 bits (constant per cycle). Transient: 1,277,943 steps + ActInit + 8 repacks.
  87 (same table renamed, other start): hub in B, 3,844,054-step transient (27 repacks), 29,113-step cycle, same +2/42/270.
- Requirements for reuse: a hub that recurs with (i) one or more periodic blocks whose count grows by a constant per
  cycle, (ii) arbitrary "frozen" content that the head crosses with a content-independent rule (letter-wise
  transducer; complement allowed), (iii) everything else bounded and identical at each hub. Then one symbolic cycle
  run with w, c abstract decides it. Signature in simulation: sqrt bouncer; long periodic block growing by whole
  periods; an irregular stretch that only grows at its ends; the 216-cell "wall" the repo saw = u_bot (270 letters =
  5 x 216 cells).

## PR 96 / PR 104: RLE token machine + chain accelerator + parity-closed affine hub map (`stepAutoK`, `SymNat`)
- Tokens: L {z=0, o=1, p=011, ab=10}, R {z, o, q=001, ba=01} with binary `N` counts; `stepBaseK` (bounded prefix
  sim + sweep rules) and `stepChainK` (affine update of unbounded alternating chains under `SafeProg` guards).
- Hub `hubState idx n`: head at right end (C in 96, A in 104), left = cap_idx (100)^b 1010 (100)^a 1, b = 12(n+4)+r_idx,
  a = 4b+d_idx, idx < 16. 32 certificates `checkSymRuleK`: run the accelerator on `SymNat` (sa*m+sb) lengths from
  hub(idx, 2m+p) to hub(idx', 3m+q), 846..1,343 steps each; `symStep*_comm` gives soundness for every m. Total map,
  no halting branch. Transient: 2+3,149,825 steps (96, to idx 2); 0+2,122,236 steps (104, to idx 4, n0 302 bits).
  The 32 rules (and step counts) are byte-identical between 96 and 104.
- Requirements: a Collatz-like map on hub parameters that is *total* (every residue branch returns to the hub family,
  no halting residue) with finitely many phases, and run lengths that are affine in the parameter during one round
  (chains handled by the affine chain accelerator). Antihydra-type maps with a reachable halting branch are excluded.

## PR 90: decoupled queue reservoir at a wall, linear fuel invariant (`CTree`, `fuelRW`, `ReachWallCore`)
- Segment m = 1^9 0 (1^5 0)^m 1^4 (right side); conduit tree `CTree` of segments; right wall = list s of segments +
  `RWallShape` (4 shapes). `bounceRW` = deterministic local update of the far segment/wall; proved `wall_bounce_plus`:
  head crosses the whole list (any sizes) right, bounces, crosses back; fuel(s,w) = sum(2m+5) + wall drops by exactly 1.
- Macro stepper `stepOne` treats the reservoir as an opaque `RWall` and counts bounces; `ReachWallCore` soundness
  quantifies over all (s, w) with fuel >= bounces+4. Certificate: 4,427,140 steps to entry (3,031 reservoir segments,
  fuel >= 43,211, 986 fixed top segments) + 3,453,426-step cycle: 43,207 bounces, left side and top reproduced, 6,505
  new segments with fuel >= 43,207 appended at the inner end. Invariant fuel >= 43,211 closes by arithmetic.
- Requirements: a far-end structure consumed one unit per visit whose consumption never feeds back into the rest
  (the head's return state/tape is independent of the reservoir content), plus a cycle that refills at least as much
  as it uses. Signature: "sea" of one block with defects; a stretch of tape that is only rewritten at the far end.

## PR 94 (halts): exact replay with a self-validated DP table of counter exhaustions
- RLE tokens; word = list of `0 1^(2u+1)` tokens (UList), left side may hold `Lpairs len val` (binary in cell pairs).
  Psi = one excursion into the word (`ustepPsi_sound`). For fronts in {01, 0111} only, a ZChain (iterated core loop)
  from width-W configuration `W_stalled(x,y)` (W = x+2y) ends at `W_stalled(.,py)` after m iterations: table
  `LCellSpec W y py m` for W in [4, 4584), y <= W/2 (T8192 x T4096 radix trees), built sequentially from 1-bit hints
  and checked row by row; `DValid k` table for runs of k-1 0111 tokens built from it.
- `stepMacro` fuses RLE steps + table jumps; `cert_ok` replays 604,910 macro steps (32,833 exhaustion lookups,
  ~3,180-bit counters, step count in pure inductive base-64 `Big96`) to `Chalt` (E reads 0): ~3.123449e957 steps.
- Requirements: a halting run whose slow phases are iterations of one parametrised sub-process (here counter exhaustion
  by width) whose outcome table is finite over the widths actually met and can be built incrementally; total macro
  steps ~1e6. Works for halting "clock + word" machines whose orbit is long but whose accelerated description is short.

## Candidates (decision "open", names as in BB6_holdouts_608.txt)
1. `1RB0LB_1RC1LC_1LD1RE_---0LA_1LE0RF_1RA0LF` (85/87 technique): repo summary: block (10101001)^n next to the left
   end grows ~50 copies per long cycle, behind it a long irregular but *slowly changing* stretch: crystal + carried word.
2. `1RB0LB_1RC1LC_1LD1RE_---0LA_1RE0RF_1RA0LF` (85/87): twin of 1 (E0 differs), same reported behaviour.
3. `1RB1LE_0RC---_1RD0LA_1RE0RB_0LA0LF_0LD1LF` (96/104): tape is long blocks of `100` separated by short markers
   (repo: `1010`) (sim at 2e8: `(001)^3713 1 (001)^5216 ... (001)^638 ... (001)^381`), the hub alphabet of PRs 96/104; base-4
   trip schedule; refill rule open. Needs more than two runs per hub, so the symbolic family is bigger.
4. `1RB1LE_1LC1RC_1LA1RD_1LD0RB_0LC0LF_0LB---` (96/104): X' = (3X+c)/2 with c set by X mod 6 plus a slowly growing
   tail; "halting condition not understood", i.e. no halting branch identified, so a total parity/residue hub map may exist.
5. `1RB---_1RC1RE_1LD0LE_1RF0LC_0RD0RA_0RB1RD` (96/104): ~10/3 map whose residue mod 3 edits a word; repo found *no*
   halting word (its 8/3 siblings do have reachable halting words and are poorer candidates).
6. `1RB0LC_1LA0RE_0LD0LB_1RA1LD_0RC1RF_0RA---` (90): reservoir (010)^n at the right consumed ~6 per pass while units
   (010)^17 (100)^16 1 are emitted at the left; levels take over when it empties: a queue/fuel picture, but nested.
7. `1RB0LB_0LC0RD_1LA1LB_0RE---_0RF1RD_1RB1RE` (85/87 or 90): list of counters (01)^n swept end to end, only a zone near
   the right end changes, finished counters freeze on the left: an ever-growing frozen list crossed uniformly.
8. `1RB0LB_0RC0LD_1LD1RE_0LA0RF_1RB0RD_0RB---` (94, halting side): PR59 visit law shared with machines proved to halt
   in round 161,211 (Lean, native_decide); an exact table-driven replay of the stream rewriting is the natural attack
   (same for `1RB0LB_0RC0LF_1LD1RE_0LA0RB_0RD0RF_0LA---` and `1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD---`).

Caveat: candidates come from the repo's own summaries plus one quick simulation (no. 3); a generic "frozen interior"
screen did not discriminate (letters are re-encoded between sweep phases, so snapshots must be taken at a fixed hub
phase to compare).
