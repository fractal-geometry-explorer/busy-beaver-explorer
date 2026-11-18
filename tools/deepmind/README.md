# Compiling DeepMind's BB(6) proofs

[google-deepmind/cryptids](https://github.com/google-deepmind/cryptids) (commit `3647718`, 12 November 2026, Lean `v4.35.0-rc4` with Mathlib) proves results about 118 machines on our holdout list. We compiled the 26 of those proofs that matter most to us on 17 November 2026. `build.sh` here repeats the build and the audit.

## What compiled

**11 machines are settled there and open in our list. All 11 compile.** Each theorem is exactly `IsHalt target` or `IsNotHalt target` from the blank tape. Here `target` is `(load_rle_machine% "<name>").toBB`. `Bridge.lean` proves that this is equivalent to the plain `ConjectureMachines.Halts` (state 0, blank tape).

| Machine | Result | Theorem | Module time |
| :--- | :--- | :--- | ---: |
| `1RB0LF_1RC0RA_1LD0RB_0LE0LC_0LA0LC_0LB---` (A6; also busycoq PR 51) | never halts | `is_not_halt` | 206 s |
| `1RB1RA_0LC0RA_1RC1LD_0LB1LE_1LF0RC_---0LD` (busycoq PR 44, Alk) | never halts | `is_not_halt` | 144 s |
| `1RB0RA_1RC0LC_0LD1RF_1RA1LE_1LD0LB_0RE---` (PR 48) | never halts | `is_not_halt` | 40 s |
| `1RB0RA_0RC0LD_1LA1RF_1LE1LD_1LB1RE_---1RA` (PR 50) | never halts | `is_not_halt` | 3 s (+162 s shared) |
| `1RB1RA_1RC1LB_0LD0RA_1RF1LE_---1LF_1LC0LF` (PR 50) | never halts | `is_not_halt` | 15 s |
| `1RB0LC_1LC0RB_0LE0LD_1LC---_0RA1LF_1LA1LF` (PR 52) | never halts | `is_not_halt` | 164 s |
| `1RB0RA_0RC0LE_1LD1RF_1LB1RD_1LD1LE_---1RA` (PR 53) | never halts | `is_not_halt` | 143 s |
| `1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LB---` (PR 47) | halts | `is_halt` | 251 s |
| `1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RC---_1LD0RA` (PR 47) | halts | `is_halt` | 114 s |
| `1RB0RE_1RC0RA_0LD0LB_0LA1LE_1LC1LF_0LA---` (PR 49) | halts | `is_halt` | 52 s |
| `1RB1RF_0RC0RE_0RD1RA_1LE0LA_1LB0LD_0RD---` (PR 49) | halts | `is_halt` | 75 s |

**How these relate to the busycoq pull requests.** The PR numbers in the table are open busycoq pull requests with a Rocq proof of the same machine. None is merged: busycoq's BB6 branch has not moved since 3 November 2026 (checked with git on 17 November).

- PRs 47 to 53 are by Alex Havrilla of DeepMind, opened on 3 November. They are Rocq versions of DeepMind's own Lean proofs, which appeared in cryptids on 6 November (cryptids PR #23). The Lean is the original, not a port of the Rocq.
- PR 44 is by Alk, who is not with DeepMind. DeepMind's Lean proof of `1RB1RA_0LC0RA_1RC1LD_0LB1LE_1LF0RC_---0LD` came later (cryptids PR #28, 11 November), uses a different method (a symbolic certificate), and does not cite PR 44.
- A6 (`1RB0LF_1RC0RA_1LD0RB_0LE0LC_0LA0LC_0LB---`) is cryptids PR #21 (31 October), with its own reflective RLE engine. Havrilla's busycoq PR 51 proves the same machine in Rocq.
- DeepMind's earlier busycoq PRs 19 to 23 (15 October, Havrilla, 27 machines) were merged. None of those machines is on our list.

**15 machines have a halts-iff map that only DeepMind has. All 15 compile.** Each one has `isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start`, and 10 of them also have a `highLevel` version. They are listed in `maps.txt`, and the times are in `compiled_maps.json`. These maps are proved without conditions. Ours for `1RB1LF_0RC1RD_1LA1LD_1LE0RA_---1LC_0LA1LA` used to assume the orbit never meets a `.small` case; it is now unconditional.

## Using them in our Lean: cited axioms

Our library cannot import these proofs: they are stated on Mathlib's Turing machines and our library is core Lean.
So `axioms.py` states each result on our definitions as a Lean `axiom`, one file per machine, listed in the machine's
`lean/check.sh`:

- **The 11 settled machines**: `holdouts/<M>/lean/DeepMind.lean` has `deepmind_halts : HaltsFromBlank` or
  `deepmind_not_halts : ¬ HaltsFromBlank`.
- **12 of the 15 maps** (the 3 others are proved here: `Map.lean`, `Iff.lean`, `DMMap.lean`):
  `holdouts/<M>/lean/DeepMindMap.lean` copies DeepMind's `State`, `start`, `next` and the definitions `next` uses,
  unchanged but for `ℕ` → `Nat`, into a namespace `DM`, and has `deepmind_halts_iff : HaltsFromBlank ↔ ∃ n,
  (DM.orbit n).isNone = true`. `orbits.sh` runs the copies and DeepMind's own maps from `start` and compares the
  states: 120 steps for each, 7 for `1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LF---_0RA1LA`, whose `next` gets slow in the
  interpreter as its numbers grow.

What an axiom rests on: DeepMind's proof (compiled here, standard axioms only), the check that their table is the
machine's, and the reading of their halting (Mathlib's semantics, blank tape, state A) as our `TM.Halts trans
(TM.blankCfg .A)`, which no proof checks. Nothing proves the axioms here. `#print axioms` names them in every theorem
that uses them, and the ledgers list them at their own level, *cited*. A proof here (as in
`holdouts/1RB1RD_1LC0RD_1RF1RB_1LE0RA_0LB0LE_---0RC/lean/DMMap.lean`), or one bridge theorem between the two
semantics, turns an axiom into a theorem with the same statement.

    python3 tools/deepmind/axioms.py tools/deepmind/compiled.json tools/deepmind/compiled_maps.json CRYPTIDS_DIR
    tools/deepmind/orbits.sh CRYPTIDS_DIR

## Checks

- **Axioms.** `#print axioms` on every theorem lists only `propext`, `Classical.choice` and `Quot.sound`. There is no `sorryAx`, no `native_decide` (`Lean.ofReduceBool`) and no extra axiom.
- **The right machine.** `Audit.lean` and `AuditMaps.lean` evaluate each compiled `machine.transition` table and print it in bbchallenge notation. All 26 match their names in `BB6_holdouts_608.txt` character for character.
- **Running the maps.** For 6 of the 15 maps we ran `next` for 20,000 steps from `start`, and none halted. The others grow too fast to iterate in Lean's interpreter.

## Cost

- **Mathlib.** `cache.mathlib.org` and `release.lean-lang.org` are blocked in our cloud sandbox. So the toolchain came from the GitHub release, and Mathlib was built from source. That build, together with the framework and the first module, took 50 minutes on 4 cores.
- **The proofs.** After that, the 11 proofs took 7 minutes and the 15 maps 6.5 minutes.
