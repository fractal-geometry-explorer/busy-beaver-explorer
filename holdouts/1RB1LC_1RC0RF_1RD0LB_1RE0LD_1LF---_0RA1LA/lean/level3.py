"""Generate Level3Rules.lean and Level3.lean: the resets of 1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LF---_0RA1LA at the short
tails that the level-2 resets leave (`x3`, `tl 0 y`, `s2` right after the d block), and at every short tail that those
lead to, until the list closes (`py/closure_table.py` found it; output in `runs/closure_table.txt`).  One new suffix
appears, `s3` = `1011001` (the third level, `cfg 17 0 (tl (n+k) s3)`); its nearly empty tails are here too.

usage: python3 level3.py   (writes both files next to this script; needs nearempty.py next to it)

Each rule is proved along the symbolic run (`tools/py/bbtools/symframe.py`), for every n (n = 2a, 2a + 1 where the end
depends on the parity; from n + 1 or n + 2 where the run needs that many words 1100).
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import nearempty as ne  # noqa: E402
from nearempty import M, C, D, W, CS, DS, S2, analyse, cells, Machine_parse  # noqa: E402
from bbtools.symframe import prove_framed, Library  # noqa: E402
from bbtools.symtm import run, Config, ProofError  # noqa: E402

S3 = "1 0 1 1 0 0 1"
# short tails: cells before 0^inf, Lean term, the Lean def (name, doc) if new here
TAILS = {
    "s0": ("0 1", "s0"), "t1001": ("1 0 0 1", "tl 0 s0"), "s2": (S2, "s2"),
    "x3": ("1 1 0 0 1 0 1 1 0 0 1", "x3"), "y0": ("1 0 1 1 0 1 0 0 1", "tl 0 y"),
    "z1": ("0 1 0 1 1 0 0 1", "z1"), "z2": ("1 0 0 1 0 1 1 0 0 1", "z2"), "x4": ("1 1 0 1 1 0 1 1 0 0 1", "x4"),
    "z3": ("1 1 0 1 1 0 0 1", "z3"), "z4": ("1 1 0 0 1", "z4"),
}
SUFFIX = {"s1": "1", "s2": S2, "s3": S3}
NEWDEFS = ["z1", "z2", "x4", "z3", "z4"]


def start(lbl):
    """A start label: a short tail, or ('s3', t)."""
    if isinstance(lbl, tuple):
        s, t = lbl
        return " ".join(["1 0"] + ["1 1 1 0"] * t + [SUFFIX[s]]), f"tl {t} {s}", f"{s}_t{t}"
    return TAILS[lbl][0], TAILS[lbl][1], lbl


# (start, r): outcome.  ("n", k, m, T): cfg (n+k) m T; ("ten", (c_even, c_odd), T): cfg 10 (a+c) T for n = 2a, 2a+1;
# ("long", k, s): cfg 17 0 (tl (n+k) s); ("loop", k): cfg (n+k) 0 s0; ("halt",).
TABLE = [
    ("x3", 0, ("n", 4, 0, "t1001")), ("x3", 1, ("n", 3, 1, "z1")), ("x3", 2, ("long", 14, "s2")),
    ("x3", 3, ("ten", (14, 14), "t1001")), ("x3", 4, ("loop", 41)),
    ("y0", 0, ("long", 3, "s1")), ("y0", 1, ("ten", (5, 5), "t1001")), ("y0", 2, ("halt",)),
    ("y0", 3, ("n", 26, 0, "t1001")), ("y0", 4, ("loop", 30)),
    ("s2", 0, ("long", 3, "s3")), ("s2", 1, ("loop", 16)), ("s2", 2, ("n", 22, 0, "t1001")),
    ("s2", 3, ("loop", 32)), ("s2", 4, ("loop", 43)),
    ("z1", 1, ("n", 6, 0, "z2")), ("z2", 0, ("loop", 5)),
    (("s3", 0), 0, ("long", 3, "s1")), (("s3", 0), 1, ("loop", 21)), (("s3", 0), 2, ("loop", 20)),
    (("s3", 0), 3, ("loop", 31)), (("s3", 0), 4, ("n", 31, 0, "t1001")),
    (("s3", 1), 0, ("loop", 11)), (("s3", 1), 2, ("loop", 24)), (("s3", 1), 3, ("n", 30, 0, "t1001")),
    (("s3", 1), 4, ("ten", (13, 13), "x4")),
    (("s3", 2), 0, ("n", 10, 0, "t1001")), (("s3", 2), 2, ("long", 23, "s3")), (("s3", 2), 3, ("ten", (12, 13), "x4")),
    (("s3", 3), 0, ("ten", (2, 3), "x4")), (("s3", 3), 2, ("loop", 41)),
    ("x4", 0, ("loop", 9)), ("x4", 1, ("n", 3, 1, "z3")), ("x4", 2, ("long", 21, "s1")), ("x4", 3, ("loop", 39)),
    ("x4", 4, ("loop", 32)),
    ("z3", 1, ("n", 3, 1, "z4")), ("z4", 1, ("n", 3, 1, "s0")), ("s0", 1, ("n", 6, 0, "t1001")),
]

LIB = Library("l3_")
SIMP = "cfg, tl, s0, s1, s2, s3, x3, y, x4, z1, z2, z3, z4, rep_zero, app_cons, app_nil"


def bits(s):
    return "[" + ", ".join("true" if x == "1" else "false" for x in s.split()) + "]"


def one(lbl, r, outc, cond):
    st_cells, st_lean, base = start(lbl)
    base = f"{base}_r{r}"
    if outc[0] == "ten":
        variants = [("even", "(11001100)^a", "2 * a", outc[1][0]), ("odd", "1100 (11001100)^a", "2 * a + 1", outc[1][1])]
    else:
        blk, nexp = {0: ("(1100)^n", "n"), 1: ("(1100)^n+1", "n + 1"), 2: ("(1100)^n+2", "n + 2")}[cond]
        variants = [("", blk, nexp, None)]
    raws, outs = [], []
    for vname, blk, nexp, cc in variants:
        name = base + (f"_{vname}" if vname else "")
        st = f"0^inf B> 0 0 1 {blk} {' '.join([DS] * r)} {st_cells} 0^inf"
        off = cond if outc[0] != "ten" else 0
        var = "a" if outc[0] == "ten" else "n"
        lhs = f"cfg ({nexp}) {r} ({st_lean})"
        if outc[0] == "halt":
            cfg0 = Config.parse(st)
            end = run(Machine_parse(), cfg0.copy(), lambda c: c.state == 4 and c.right and c.right[0] == 1,
                      max_moves=10 ** 6, rotate=True)
        elif outc[0] == "n":
            _, k, m, T = outc
            end = f"0^inf B> 0 0 1 (1100)^n {' '.join([CS] * (k + off))} {' '.join([DS] * m)} {TAILS[T][0]} 0^inf"
        elif outc[0] == "loop":
            end = f"0^inf B> 0 0 1 (1100)^n {' '.join([CS] * (outc[1] + off))} 0 1 0^inf"
        elif outc[0] == "long":
            k = outc[1] + off
            kk = f"(1110)^n+{k}" if k > 0 else "(1110)^n"
            end = f"0^inf B> 0 0 1 {' '.join([CS] * 17)} 1 0 {kk} {SUFFIX[outc[2]]} 0^inf"
        else:
            end = f"0^inf B> 0 0 1 {' '.join([CS] * 10)} {' '.join([DS] * cc)} ({DS})^a {TAILS[outc[2]][0]} 0^inf"
        txt, fin = prove_framed(M, name + "_raw", st, end, max_seg=30, rotate=True, max_moves=10 ** 6, lib=LIB)
        raws.append(txt)
        K = fin.steps.lean()
        if outc[0] == "halt":
            outs.append(f"/-- The machine halts after {K} + 1 steps, for every n. -/\n"
                        f"theorem {name}_halts (n : Nat) : Halts trans ({lhs}) := by\n"
                        f"  have h := {name}_raw n\n  simp only [{SIMP}]\n  exact ⟨_, _, h, rfl⟩\n")
            continue
        pf = [f"  have h := {name}_raw {var}"]
        goal_rw = []
        if outc[0] == "ten":
            goal_rw.append("rep_two_mul a" if vname == "even" else "rep_succ (2 * a), rep_two_mul a")
        if outc[0] in ("n", "loop"):
            if outc[0] == "n":
                m, tname = outc[2], TAILS[outc[3]][1]
                tcells = list(D) * m + cells(TAILS[outc[3]][0])
            else:
                m, tname, tcells = 0, "s0", [0, 1]
            rot, e, j, l, z = analyse(fin, [0, 0, 1], C, tcells)
            total = f"{e} + {j + l}"
            rhs = f"cfg ({total}) {m} ({tname})"
            goal_rw.append(f"rep_eq_split {j} ({e}) {l} (m := {total}) (by omega)")
        elif outc[0] == "long":
            rot, e, j, l, z = analyse(fin, [0, 0, 1] + list(C) * 17 + [1, 0], W, cells(SUFFIX[outc[2]]))
            total = f"{e} + {j + l}" if j + l else e
            rhs = f"cfg 17 0 (tl ({total}) {outc[2]})"
            if j + l:
                goal_rw.append(f"rep_eq_split {j} ({e}) {l} (m := {total}) (by omega)")
        else:
            tname = TAILS[outc[2]][1]
            rot, e, j, l, z = analyse(fin, [0, 0, 1] + list(C) * 10, D, cells(TAILS[outc[2]][0]))
            total = f"{e} + {j + l}"
            rhs = f"cfg 10 ({total}) ({tname})"
            goal_rw.append(f"rep_eq_split {j} ({e}) {l} (m := {total}) (by omega)")
        if rot:
            pf.append(f"  have e : {rot[1]} = {rot[2]} := {rot[0]}")
            pf.append("  rw [e] at h")
        if z:
            pf.append("  simp only [cons_false_blank] at h")
        pf.append(f"  simp only [{SIMP}]")
        if goal_rw:
            pf.append(f"  rw [{', '.join(goal_rw)}]")
        pf.append("  exact h")
        outs.append(f"theorem {name} ({var} : Nat) :\n    steps ({K}) ({lhs}) = some ({rhs}) := by\n" + "\n".join(pf) + "\n")
        if outc[0] == "loop":
            outs.append(f"theorem {name}_never_halts ({var} : Nat) : ¬ Halts trans ({lhs}) :=\n"
                        f"  never_halts_of_reach ({name} {var}) (loop_runs' _ (by omega))\n")
        print(name, K, "->", rhs, file=sys.stderr)
    return raws, outs


HEAD = """import NearEmpty
import Level3Rules

/-!
# 1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LF---_0RA1LA: the third level, in `cfg` form

Generated by `level3.py` (the rules of `Level3Rules.lean` restated); do not edit by hand.  Some resets of level 2
(`NearEmpty.lean`) leave a short tail that is not a nearly empty tail of a suffix: `x3`, `tl 0 y`, or `s2` right after
the d block.  Here is the reset at each of them for every r that occurs, and at each short tail those lead to, until
nothing new comes: 39 rules, for every n.  One new suffix appears, `s3` = `1011001`: from `cfg n 0 s2` the machine
builds the long tail `cfg 17 0 (tl (n+3) s3)`, the third level, and its nearly empty tails are here too.  The other
ends: the tail `1001` of level 0 (`tl 0 s0`, whose resets are in `BlankRun.lean` and `NearEmpty.lean`), a long tail of
suffix `s1` or `s2` (a new level 1 or 2), the loop record `cfg (n+k) 0 s0` (never halts), or, for
`cfg (n+1) 2 (tl 0 y)`, a halt.

`s3` = `1 0 1 1 0 0 1 0^inf`, `x4` = `1 1 0 1 1 0 1 1 0 0 1 0^inf`, `z1` = `0 1 0 1 1 0 0 1 0^inf`,
`z2` = `1 0 0 1 0 1 1 0 0 1 0^inf`, `z3` = `1 1 0 1 1 0 0 1 0^inf`, `z4` = `1 1 0 0 1 0^inf`.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

namespace H66813

open TM

"""

TAIL = """
/-- The second halting class is reached by the generic rows: a nearly empty phase end (n, 2, 1) of level 2 with
n = 6 or 7 mod 10 resets to (10, floor(n/2) + 9) with the tail `tl 0 y`, whose periods end at r = 2: the machine
halts. -/
theorem s2_r2_t1_to_y_halts (a : Nat) (ha : a % 5 = 3) :
    Halts trans (cfg (2 * a) 2 (tl 1 s2)) ∧ Halts trans (cfg (2 * a + 1) 2 (tl 1 s2)) := by
  obtain ⟨q, rfl⟩ : ∃ q, a = 5 * q + 3 := ⟨a / 5, by omega⟩
  have hp := periods_s (q + 2) 10 2 (tl 0 y)
  rw [show 2 + 5 * (q + 2) = 5 * q + 3 + 9 by omega] at hp
  have hy := y0_r2_halts (10 + 31 * (q + 2))
  exact ⟨halts_of_reach (steps_seq trans (s2_r2_t1_even _) hp) hy,
    halts_of_reach (steps_seq trans (s2_r2_t1_odd _) hp) hy⟩

end H66813
"""


def main():
    raws, outs = [], []
    for lbl, r, outc in TABLE:
        for cond in (0, 1, 2):
            try:
                rw, ot = one(lbl, r, outc, cond)
                break
            except (ProofError, AssertionError, ValueError) as e:
                print(f"{lbl} r{r} cond {cond}: {type(e).__name__} {str(e)[:200]}", file=sys.stderr)
        else:
            raise SystemExit(f"no proof for {lbl} r{r}")
        raws += rw
        outs += ot
    defs = ["/-- The third-level suffix: `tl t s3` = `1 0 (1110)^t 1011001 0^inf`. -/\n"
            f"def s3 : Tape := app {bits(S3)} blank\n"]
    for nm in NEWDEFS:
        defs.append(f"/-- A short tail: `{TAILS[nm][0]} 0^inf`. -/\ndef {nm} : Tape := app {bits(TAILS[nm][0])} blank\n")
    rf = ne.rules_file("Machine", "H66813", ["/-! The pieces: windows, crossings and re-bracketings, each stated once. -/\n"
                                              + LIB.text()] + raws,
                       f"Resets of {M} at the short tails of the third level, generated by `level3.py`; do not edit by "
                       "hand.")
    rf = rf.replace("namespace H66813", "set_option maxHeartbeats 4000000\nset_option maxRecDepth 10000\n\nnamespace H66813", 1)
    open(os.path.join(HERE, "Level3Rules.lean"), "w").write(rf)
    open(os.path.join(HERE, "Level3.lean"), "w").write(HEAD + "\n".join(defs) + "\n" + "\n".join(outs) + TAIL)


if __name__ == "__main__":
    main()
