# Compiling DeepMind's BB(6) proofs

[google-deepmind/cryptids](https://github.com/google-deepmind/cryptids) (commit `3647718`, 12 November 2026, Lean `v4.35.0-rc4` with Mathlib) proves results about 118 machines on our holdout list. We compiled the 26 of those proofs that matter most to us on 17 November 2026. `build.sh` here repeats the build and the audit.

## What compiled

**11 machines are settled there and open in our list. All 11 compile.** Each theorem is exactly `IsHalt target` or `IsNotHalt target` from the blank tape. Here `target` is `(load_rle_machine% "<name>").toBB`. `Bridge.lean` proves that this is equivalent to the plain `ConjectureMachines.Halts` (state 0, blank tape).

| Machine | Result | Theorem | Module time |
| :--- | :--- | :--- | ---: |
| `1RB0LF_1RC0RA_1LD0RB_0LE0LC_0LA0LC_0LB---` (A6) | never halts | `is_not_halt` | 206 s |
| `1RB1RA_0LC0RA_1RC1LD_0LB1LE_1LF0RC_---0LD` (busycoq PR 44) | never halts | `is_not_halt` | 144 s |
| `1RB0RA_1RC0LC_0LD1RF_1RA1LE_1LD0LB_0RE---` (PR 48) | never halts | `is_not_halt` | 40 s |
| `1RB0RA_0RC0LD_1LA1RF_1LE1LD_1LB1RE_---1RA` (PR 50) | never halts | `is_not_halt` | 3 s (+162 s shared) |
| `1RB1RA_1RC1LB_0LD0RA_1RF1LE_---1LF_1LC0LF` (PR 50) | never halts | `is_not_halt` | 15 s |
| `1RB0LC_1LC0RB_0LE0LD_1LC---_0RA1LF_1LA1LF` (PR 52) | never halts | `is_not_halt` | 164 s |
| `1RB0RA_0RC0LE_1LD1RF_1LB1RD_1LD1LE_---1RA` (PR 53) | never halts | `is_not_halt` | 143 s |
| `1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LB---` (PR 47) | halts | `is_halt` | 251 s |
| `1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RC---_1LD0RA` (PR 47) | halts | `is_halt` | 114 s |
| `1RB0RE_1RC0RA_0LD0LB_0LA1LE_1LC1LF_0LA---` (PR 49) | halts | `is_halt` | 52 s |
| `1RB1RF_0RC0RE_0RD1RA_1LE0LA_1LB0LD_0RD---` (PR 49) | halts | `is_halt` | 75 s |

**15 machines have a halts-iff map that only DeepMind has. All 15 compile.** Each one has `isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start`, and 10 of them also have a `highLevel` version. They are listed in `maps.txt`, and the times are in `compiled_maps.json`. These maps are proved without conditions. Ours for `1RB1LF_0RC1RD_1LA1LD_1LE0RA_---1LC_0LA1LA` assumes the orbit never meets a `.small` case.

## Checks

- **Axioms.** `#print axioms` on every theorem lists only `propext`, `Classical.choice` and `Quot.sound`. There is no `sorryAx`, no `native_decide` (`Lean.ofReduceBool`) and no extra axiom.
- **The right machine.** `Audit.lean` and `AuditMaps.lean` evaluate each compiled `machine.transition` table and print it in bbchallenge notation. All 26 match their names in `BB6_holdouts_608.txt` character for character.
- **Running the maps.** For 6 of the 15 maps we ran `next` for 20,000 steps from `start`, and none halted. The others grow too fast to iterate in Lean's interpreter.

## Cost

- **Mathlib.** `cache.mathlib.org` and `release.lean-lang.org` are blocked in our cloud sandbox. So the toolchain came from the GitHub release, and Mathlib was built from source. That build, together with the framework and the first module, took 50 minutes on 4 cores.
- **The proofs.** After that, the 11 proofs took 7 minutes and the 15 maps 6.5 minutes.
