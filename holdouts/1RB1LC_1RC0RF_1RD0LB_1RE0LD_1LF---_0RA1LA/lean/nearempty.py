"""Generate NearEmptyRules.lean and NearEmpty.lean: every reset of 1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LF---_0RA1LA at a
nearly empty tail (t below what the row of the reset table reads), for the three suffixes the run has: `1001` (before
level 1), `1` (level 1) and `1001101011001` (level 2), blank tape after the suffix.  Each rule is proved along the
symbolic run (tools/py/bbtools/symtm.py, as resets.py) for every n (per parity of n where the end depends on it).

usage: python3 nearempty.py   (writes both files next to this script)

NearEmptyRules.lean has the rules as the run writes them (`*_raw`); NearEmpty.lean restates them in the `cfg` form of
Periods.lean, with the tapes `tl t s` of BlankRun.lean, and adds the loop rule `loop5`, the halting rule and what
follows from them (`*_never_halts`, `s2_r2_t2_halts`).  The outcomes (found by running the plain machine for
n = 60..65, `py/nearempty_table.py`) are of four kinds:

* `cfg (n+k) 0 T` or `cfg 10 m' T`: a new record with a short tail T (`tl 0 s0` = `1001`, `s2`, `x3`, `tl 0 y`);
* `cfg 17 0 (tl (n+k) s)`: a new long tail of n+k words 1110 is built (the next level);
* `cfg (n+k) 0 s0`: the record `0^inf B> 0 0 1 (1100)^(n+k) 0 1 0^inf`, from which `loop5` adds five words 1100 a
  round forever: that class never halts;
* a halt (suffix `1001101011001`, r = 2, t = 2).
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "..", "tools", "py"))
import bbtools.symtm as symtm  # noqa: E402
from bbtools.symframe import prove_framed, Library  # noqa: E402
from bbtools.symtm import run, Config, Rep, Blank, right_term, rules_file, lin  # noqa: E402

symtm.MAX_CARRY = 8

M = "1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LF---_0RA1LA"
C, D, W = (1, 1, 0, 0), (1, 0, 1, 1, 0, 1, 1, 0), (1, 1, 1, 0)
CS, DS = "1100", "10110110"
S2 = "1 0 0 1 1 0 1 0 1 1 0 0 1"
# the short tails, as cells before 0^inf, and their Lean names (BlankRun.lean / NearEmpty.lean)
TAILS = {"s0": ("0 1", "s0"), "t1001": ("1 0 0 1", "tl 0 s0"), "s1": ("1", "s1"), "s2": (S2, "s2"),
         "x3": ("1 1 0 0 1 0 1 1 0 0 1", "x3"), "y": ("1 0 1 1 0 1 0 0 1", "tl 0 y")}
NEED = [4, 1, 4, 3, 2]


def start_tail(suf, t):
    if suf == "t1001":
        return "1 0 0 1 0^inf", "tl 0 s0"
    return " ".join(["1 0"] + ["1 1 1 0"] * t + [TAILS[suf][0], "0^inf"]), f"tl {t} {TAILS[suf][1]}"


# (suffix, r, t): outcome.  ("n", k, T): cfg (n+k) 0 T; ("ten", (c_even, c_odd), T): cfg 10 (a+c) T with n = 2a or
# 2a+1; ("long", k, s): cfg 17 0 (tl (n+k) s); ("loop", k): cfg (n+k) 0 s0; ("halt",).  `n1`: the rule needs n >= 1
# (stated for n+1), `n2`: n >= 2.
TABLE = [
    ("t1001", 3, 0, ("loop", 38), "n1"), ("t1001", 4, 0, ("loop", 28), ""),
    ("s1", 0, 0, ("long", -2, "s2"), "n2"), ("s1", 0, 1, ("long", 0, "s2"), ""), ("s1", 0, 2, ("loop", 12), ""),
    ("s1", 0, 3, ("long", 2, "s2"), ""), ("s1", 1, 0, ("loop", 9), ""), ("s1", 2, 0, ("ten", (6, 7), "t1001"), ""),
    ("s1", 2, 1, ("loop", 20), "n1"), ("s1", 2, 2, ("long", 21, "s2"), "n1"), ("s1", 2, 3, ("loop", 29), "n1"),
    ("s1", 3, 0, ("long", 20, "s2"), ""), ("s1", 3, 1, ("loop", 32), ""), ("s1", 3, 2, ("long", 22, "s2"), ""),
    ("s1", 4, 0, ("loop", 33), ""), ("s1", 4, 1, ("long", 23, "s2"), ""),
    ("s2", 0, 0, ("loop", 10), "n1"), ("s2", 0, 1, ("loop", 20), ""), ("s2", 0, 2, ("n", 7, "s2"), ""),
    ("s2", 0, 3, ("ten", (2, 3), "x3"), ""), ("s2", 1, 0, ("n", 16, "t1001"), ""), ("s2", 2, 0, ("loop", 26), ""),
    ("s2", 2, 1, ("ten", (9, 9), "y"), ""), ("s2", 2, 2, ("halt",), "n1"), ("s2", 2, 3, ("n", 36, "t1001"), "n1"),
    ("s2", 3, 0, ("loop", 40), ""), ("s2", 3, 1, ("n", 27, "s2"), ""), ("s2", 3, 2, ("ten", (12, 13), "x3"), ""),
    ("s2", 4, 0, ("n", 28, "s2"), ""), ("s2", 4, 1, ("ten", (13, 13), "x3"), ""),
]


def tok_cells(tks):
    return [x for x in tks if isinstance(x, int)]


def lit_term(cells, rest):
    acc = rest
    for x in reversed(cells):
        acc = f"cons {'true' if x else 'false'} ({acc})"
    return acc


def lword(w):
    return "[" + ", ".join("true" if x else "false" for x in w) + "]"


def analyse(fin, fixed, word, tail_cells):
    """fin.right = fixed literals, P literals, Rep(w0, e), Q literals, tail_cells, Blank.  Returns the rewrite of h
    (a rotation, or None), the count expression e, j (words of `word` in P) and l (in Q)."""
    R = fin.right
    assert isinstance(R[-1], Blank) and fin.left and isinstance(fin.left[0], Blank) and len(fin.left) == 1
    ix = [i for i, x in enumerate(R) if isinstance(x, Rep)]
    assert len(ix) == 1, R
    i = ix[0]
    rp = R[i]
    pre, post = R[:i], R[i + 1:-1]
    assert all(isinstance(x, int) for x in pre + post)
    assert list(pre[:len(fixed)]) == list(fixed), (pre, fixed)
    pre = list(pre[len(fixed):])
    post = list(post)
    zeros = 0
    while post and post[-1] == 0:
        post.pop()
        zeros += 1
    rot = None
    w0 = tuple(rp.word)
    if w0 != word:
        for k in range(1, len(word)):
            x = pre[len(pre) - k:]
            if list(x) + list(w0) == list(word) + list(x):
                rest_cells = post + [0] * zeros
                after = lit_term(rest_cells, "blank")
                lhs = lit_term(x, f"rep ({rp.n.lean()}) {lword(w0)} ({after})")
                rhs = f"rep ({rp.n.lean()}) {lword(word)} ({lit_term(x + rest_cells, 'blank')})"
                rot = (f"rep_rotate ({rp.n.lean()}) {lword(x)} {lword(w0)} {lword(word)} rfl ({after})", lhs, rhs)
                pre = pre[:len(pre) - k]
                post = list(x) + post
                break
        else:
            raise ValueError(f"no rotation of {w0} to {word}")
    assert post[len(post) - len(tail_cells):] == list(tail_cells), (post, tail_cells)
    body = post[:len(post) - len(tail_cells)] if tail_cells else post
    assert len(pre) % len(word) == 0 and len(body) % len(word) == 0, (pre, body)
    j, l = len(pre) // len(word), len(body) // len(word)
    assert all(tuple(pre[q:q + len(word)]) == word for q in range(0, len(pre), len(word)))
    assert all(tuple(body[q:q + len(word)]) == word for q in range(0, len(body), len(word)))
    return rot, rp.n.lean(), j, l, zeros


def cells(s):
    return [int(x) for x in s.split()]


LIB = Library("ne_")
SUMMARY = []

HEAD = """import BlankRun
import NearEmptyRules

/-!
# 1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LF---_0RA1LA: the resets at a nearly empty tail, in `cfg` form

Generated by `nearempty.py` (the rules of `NearEmptyRules.lean` restated); do not edit by hand.  A phase end
`cfg n r (tl t s)` with t below what row r of the reset table reads (t < 4, 1, 4, 3, 2 for r = 0..4) reads into the
suffix s.  For the suffixes of the run (`tl 0 s0` = `1001` before level 1, `s1` = `1` in level 1, `s2` =
`1001101011001` in level 2), every such reset is a theorem here, for every n (n = 2a, 2a + 1 where the end depends on
the parity).  The ends: a record with another short tail (`tl 0 s0`, `s2`, `x3`, `tl 0 y`), a new long tail
`cfg 17 0 (tl (n+k) s2)` (the next level), the loop record `cfg (n+k) 0 s0` (`*_never_halts`: `loop5` adds five
words 1100 a round, forever), or, for `cfg (n+1) 2 (tl 2 s2)`, a halt (`s2_r2_t2_halts`).

`s0` = `0 1 0^inf`, `x3` = `1 1 0 0 1 0 1 1 0 0 1 0^inf`, `tl 0 y` = `1 0 1 1 0 1 0 0 1 0^inf`.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

namespace H66813

open TM

/-- A third-level tail: `1 1 0 0 1 0 1 1 0 0 1 0^inf`. -/
def x3 : Tape := app [true, true, false, false, true, false, true, true, false, false, true] blank
/-- A third-level suffix: `tl 0 y` = `1 0 1 1 0 1 0 0 1 0^inf`. -/
def y : Tape := app [true, true, false, true, false, false, true] blank

theorem rep_eq_split (j a l : Nat) {m : Nat} (h : m = j + a + l) (w : List Bool) (s : Tape) :
    rep m w s = rep j w (rep a w (rep l w s)) := by
  subst h; exact rep_split j a l w s

theorem halts_of_reach {a : Nat} {c c' : Config} (h : steps a c = some c') (hc : Halts trans c') :
    Halts trans c := by
  obtain ⟨m, d, h1, h2⟩ := hc
  exact ⟨a + m, d, steps_seq trans h h1, h2⟩

theorem never_halts_of_reach {a : Nat} {c c' : Config} (h : steps a c = some c')
    (hc : ∀ j, ∃ s, j ≤ s ∧ ∃ d, steps s c' = some d) : ¬ Halts trans c := by
  apply not_halts_of_forall
  apply forall_of_unbounded trans (fun m => ∃ d, steps m c = some d)
  · intro j
    obtain ⟨s, hs, d, hd⟩ := hc j
    exact ⟨a + s, by omega, d, steps_seq trans h hd⟩
  · intro m hm; exact hm

"""

FOOT = """
/-! ## The loop and the halt, as statements about classes -/

/-- From the loop record the run goes on for ever (`loop5`, five words 1100 a round). -/
theorem loop_runs (n : Nat) : ∀ j, ∃ s, j ≤ s ∧ ∃ d, steps s (cfg (n + 1) 0 s0) = some d := by
  intro j
  induction j generalizing n with
  | zero => exact ⟨0, Nat.le_refl _, _, rfl⟩
  | succ j ih =>
    obtain ⟨s, hs, d, hd⟩ := ih (n + 5)
    have h := loop5 n
    rw [show n + 1 + 5 = n + 5 + 1 by omega] at h
    exact ⟨_, by omega, d, steps_seq trans h hd⟩

theorem loop_runs' (m : Nat) (hm : 1 ≤ m) : ∀ j, ∃ s, j ≤ s ∧ ∃ d, steps s (cfg m 0 s0) = some d := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  exact loop_runs n

theorem loop_never_halts (n : Nat) : ¬ Halts trans (cfg (n + 1) 0 s0) :=
  never_halts_of_reach (a := 0) rfl (loop_runs n)

"""

TAIL = """
/-- The halting class is reached by the generic rows: a phase end (n, 0, 6) with the level-2 suffix and n = 0 or 9
mod 10 resets to (10, (n+5)/2) with t = 2, whose periods end at r = 2, t = 2: the machine halts. -/
theorem s2_r0_t6_halts (n : Nat) (hn : n % 10 = 0 ∨ n % 10 = 9) : Halts trans (cfg n 0 (tl 6 s2)) := by
  have hp : phase (n, 0, 6) = some (10 + 31 * ((n + 5) / 2 / 5), 2, 2) := by
    simp only [phase, reset, show 4 ≤ 6 from by omega, ite_true, Option.map_some, Option.some.injEq, Prod.mk.injEq]
    exact ⟨trivial, by omega, trivial⟩
  have h := phase_spec hp s2
  rw [show 10 + 31 * ((n + 5) / 2 / 5) = (9 + 31 * ((n + 5) / 2 / 5)) + 1 by omega] at h
  exact halts_of_reach h (s2_r2_t2_halts _)

end H66813
"""


def prove(*a, **k):
    return prove_framed(*a, lib=LIB, **k)


def main():
    raws, outs = [], []
    for suf, r, t, outc, cond in TABLE:
        st_tail, st_lean = start_tail(suf, t)
        base = f"{suf}_r{r}_t{t}"
        if outc[0] == "ten":
            variants = [("even", "(11001100)^a", "2 * a", outc[1][0]), ("odd", "1100 (11001100)^a", "2 * a + 1", outc[1][1])]
        else:
            blk, nexp = {"": ("(1100)^n", "n"), "n1": ("(1100)^n+1", "n + 1"), "n2": ("(1100)^n+2", "n + 2")}[cond]
            variants = [("", blk, nexp, None)]
        for vname, blk, nexp, cc in variants:
            name = base + (f"_{vname}" if vname else "")
            start = f"0^inf B> 0 0 1 {blk} {' '.join([DS] * r)} {st_tail}"
            off = {"": 0, "n1": 1, "n2": 2}[cond] if outc[0] != "ten" else 0
            if outc[0] == "halt":
                cfg0 = Config.parse(start)
                fin = run(Machine_parse(), cfg0.copy(), lambda c: c.state == 4 and c.right and c.right[0] == 1,
                          max_moves=10 ** 6, rotate=True)
                end = fin
            elif outc[0] in ("n", "loop"):
                k = outc[1] + off
                tc = TAILS[outc[2]][0] if outc[0] == "n" else "0 1"
                end = f"0^inf B> 0 0 1 (1100)^n {' '.join([CS] * k)} {tc} 0^inf"
            elif outc[0] == "long":
                k = outc[1] + off
                kk = f"(1110)^n+{k}" if k > 0 else "(1110)^n"
                end = f"0^inf B> 0 0 1 {' '.join([CS] * 17)} 1 0 {kk} {TAILS[outc[2]][0]} 0^inf"
            else:
                end = f"0^inf B> 0 0 1 {' '.join([CS] * 10)} {' '.join([DS] * cc)} ({DS})^a {TAILS[outc[2]][0]} 0^inf"
            txt, fin = prove(M, name + "_raw", start, end, max_seg=30, rotate=True,
                             max_moves=10 ** 6)
            raws.append(txt)
            K = fin.steps.lean()
            var = "a" if outc[0] == "ten" else "n"
            # the cfg statement and its proof
            lhs = f"cfg ({nexp}) {r} ({st_lean})"
            pf = [f"  have h := {name}_raw {var}"]
            goal_rw = []
            if outc[0] == "ten":
                goal_rw.append("rep_two_mul a" if vname == "even" else "rep_succ (2 * a), rep_two_mul a")
            if outc[0] == "halt":
                K = fin.steps.lean()
                outs.append(f"/-- Suffix `1001101011001`, r = 2, t = 2: the machine halts after {K} + 1 steps, for "
                            f"every n. -/\ntheorem {name}_halts (n : Nat) : Halts trans ({lhs}) := by\n"
                            f"  have h := {name}_raw n\n  simp only [cfg, tl, s2, rep_zero, app_cons, app_nil]\n"
                            f"  exact ⟨_, _, h, rfl⟩\n")
                continue
            if outc[0] in ("n", "loop"):
                tname = TAILS[outc[2]][1] if outc[0] == "n" else "s0"
                tcells = cells(TAILS[outc[2]][0]) if outc[0] == "n" else [0, 1]
                rot, e, j, l, z = analyse(fin, [0, 0, 1], C, tcells)
                total = f"{e} + {j + l}"
                rhs = f"cfg ({total}) 0 ({tname})"
                goal_rw.append(f"rep_eq_split {j} ({e}) {l} (m := {total}) (by omega)")
            elif outc[0] == "long":
                tname = TAILS[outc[2]][1]
                rot, e, j, l, z = analyse(fin, [0, 0, 1] + list(C) * 17 + [1, 0], W, cells(TAILS[outc[2]][0]))
                total = f"{e} + {j + l}" if j + l else e
                rhs = f"cfg 17 0 (tl ({total}) {tname})"
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
            pf.append("  simp only [cfg, tl, s0, s1, s2, x3, y, rep_zero, app_cons, app_nil]")
            if goal_rw:
                pf.append(f"  rw [{', '.join(goal_rw)}]")
            pf.append("  exact h")
            outs.append(f"theorem {name} ({var} : Nat) :\n    steps ({K}) ({lhs}) = some ({rhs}) := by\n" + "\n".join(pf) + "\n")
            if outc[0] == "loop":
                outs.append(f"theorem {name}_never_halts ({var} : Nat) : ¬ Halts trans ({lhs}) :=\n"
                            f"  never_halts_of_reach ({name} {var}) (loop_runs' _ (by omega))\n")
            SUMMARY.append((suf, r, t, vname, lhs, rhs if outc[0] != "halt" else "halt", outc[0]))
            print(name, K, "->", rhs, file=sys.stderr)
    # the loop rule
    txt, fin = prove(M, "loop5_raw", "0^inf B> 0 0 1 (1100)^n+1 0 1 0^inf",
                     f"0^inf B> 0 0 1 (1100)^n+1 {' '.join([CS] * 5)} 0 1 0^inf", max_seg=30,
                     rotate=True, max_moves=10 ** 6)
    raws.append(txt)
    rot, e, j, l, z = analyse(fin, [0, 0, 1], C, [0, 1])
    outs.insert(0, f"/-- The loop: `0^inf B> 0 0 1 (1100)^(n+1) 0 1 0^inf` gains five words 1100 in {fin.steps.lean()} "
                   f"steps. -/\ntheorem loop5 (n : Nat) :\n    steps ({fin.steps.lean()}) (cfg (n + 1) 0 s0) = some (cfg (n + 1 + 5) 0 s0) := by\n"
                   f"  have h := loop5_raw n\n" + ("  simp only [cons_false_blank] at h\n" if z else "") + "  simp only [cfg, s0, rep_zero]\n"
                   f"  rw [rep_eq_split {j} ({e}) {l} (m := n + 1 + 5) (by omega)]\n  exact h\n")
    rf = rules_file("Machine", "H66813", ["/-! The pieces: windows, crossings and re-bracketings, each stated once. -/\n" + LIB.text()] + raws,
                    f"Resets of {M} at a nearly empty tail, generated by `nearempty.py`; do not edit by hand.")
    rf = rf.replace("namespace H66813", "set_option maxHeartbeats 4000000\nset_option maxRecDepth 10000\n\nnamespace H66813", 1)
    open(os.path.join(HERE, "NearEmptyRules.lean"), "w").write(rf)
    loop = outs.pop(0)
    open(os.path.join(HERE, "NearEmpty.lean"), "w").write(HEAD + loop + FOOT + "\n".join(outs) + TAIL)


def Machine_parse():
    from bbtools.machine import Machine
    return Machine.parse(M)


if __name__ == "__main__":
    main()
