"""Write lean/CollideQ.lean for a machine of the family 1RB?RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_X---: the rules of
Rules.lean, Transients.lean and Collide.lean restated on the configurations of Abstract.lean (`qr W a G`, raw gaps;
`zc L G`, the middle of a one-unit step), each proved by bringing both statements to one normal form
(`simp only` with the expansions and rotations listed in `NF` below).

usage (from the repository root):
  python3 holdouts/1RB0RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_0LC---/py/gen_collideq.py MACHINE > holdouts/MACHINE/lean/CollideQ.lean
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from gen_collide import TABLES  # noqa: E402

B = {"t": "true", "f": "false"}
# words whose rotations are normalised: a cell in front of a repeat of a word ending in that cell moves inside
BASE = ["t", "f", "tt", "ttt", "fff", "tf", "fft", "tttttt", "ftftft", "fftfft"]


def rotations(w):
    return {w[i:] + w[:i] for i in range(len(w))}


def lst(w):
    return "[" + ", ".join(B[c] for c in w) + "]"


def nf_lemmas():
    words = set()
    for b in BASE:
        words |= rotations(b)
    out, names = [], []
    for k, w in enumerate(sorted(words, key=lambda x: (len(x), x))):
        b, v = w[-1], w[:-1]
        w2 = b + v
        name = f"nf_rot{k}"
        names.append(name)
        out.append(f"theorem {name} (n : Nat) (X : Tape) :\n    cons {B[b]} (rep n {lst(w)} X) = rep n {lst(w2)} "
                   f"(cons {B[b]} X) :=\n  rep_rotate n [{B[b]}] {lst(w)} {lst(w2)} rfl X\n")
    return out, names


def steps_of(text, name):
    m = re.search(r"theorem " + name + r" [^\n]*\n    steps \((.*?)\) ⟨", text)
    return m.group(1)


def main():
    m = sys.argv[1]
    lean = os.path.join(HERE, "../../", m, "lean")
    mach = open(os.path.join(lean, "Machine.lean")).read()
    ns = re.search(r"^namespace (\w+)", mach, re.M).group(1)
    raw = open(os.path.join(lean, "Collide.lean")).read() + open(os.path.join(lean, "Rules.lean")).read() + \
        open(os.path.join(lean, "Transients.lean")).read()
    lem, names = nf_lemmas()
    nf = ("qr, zc, gl, wl, wlx, gl_twos, gl_twos_blank, wlx_ones, wl_append, wlx_append, rep_mul2, rep_mul3, rep_succ, rep_zero, "
          "app_cons, app_nil, cons_false_blank, List.replicate_succ, List.cons_append, List.nil_append, "
          "List.append_nil, " + ", ".join(names))
    ths = []

    def th(name, binders, n, lhs, rhs, raw_call, pre=""):
        ths.append(f"theorem {name} {binders} :\n    steps ({n}) {lhs} = some {rhs} := by\n{pre}"
                   f"  have e := {raw_call}\n  simp only [{nf}] at e ⊢\n  exact e\n")

    # word phase
    th("wq_big", "(j x : Nat) (V : List Nat) (R : Tape)", steps_of(raw, "wp_big"),
       "⟨rep 1 [true, true, true] (cons false (wl ((2 * j + 5) :: x :: V))), cons false R, .B⟩",
       "⟨cons true (cons true (cons false (wl (phi (phi ((2 * j + 5) :: x :: V)))))), cons false (cons true R), .A⟩",
       "wp_big j (wl (x :: V)) R", "  rw [phi2_big]\n")
    th("wq_three", "(x : Nat) (V : List Nat) (R : Tape)", steps_of(raw, "wp_three"),
       "⟨rep 1 [true, true, true] (cons false (wl (3 :: x :: V))), cons false R, .B⟩",
       "⟨cons true (cons true (cons false (wl (phi (phi (3 :: x :: V)))))), cons false (cons true R), .A⟩",
       "wp_three (wl (x :: V)) R", "  rw [phi2_three]\n")
    th("wq_one", "(i y : Nat) (V : List Nat) (R : Tape)", steps_of(raw, "wp_one"),
       "⟨rep 1 [true, true, true] (cons false (wl (1 :: (2 * i + 1) :: y :: V))), cons false R, .B⟩",
       "⟨cons true (cons true (cons false (wl (phi (phi (1 :: (2 * i + 1) :: y :: V)))))), cons false (cons true R), .A⟩",
       "wp_one i (wl (y :: V)) R", "  rw [phi2_one]\n")
    # wide steps
    th("qw_big", "(a j x : Nat) (V G : List Nat)", steps_of(raw, "q_big_wide"),
       "(qr ((2 * j + 5) :: x :: V) (a + 2) G)", "(qr (phi (phi ((2 * j + 5) :: x :: V))) 1 ((3 * a + 2) :: G))",
       "q_big_wide a j (wl (x :: V)) (gl G)", "  rw [phi2_big]\n")
    th("qw_three", "(a x : Nat) (V G : List Nat)", steps_of(raw, "q_three_wide"),
       "(qr (3 :: x :: V) (a + 2) G)", "(qr (phi (phi (3 :: x :: V))) 1 ((3 * a + 2) :: G))",
       "q_three_wide a (wl (x :: V)) (gl G)", "  rw [phi2_three]\n")
    th("qw_one", "(a i y : Nat) (V G : List Nat)", steps_of(raw, "q_one_wide"),
       "(qr (1 :: (2 * i + 1) :: y :: V) (a + 2) G)",
       "(qr (phi (phi (1 :: (2 * i + 1) :: y :: V))) 1 ((3 * a + 2) :: G))",
       "q_one_wide a i (wl (y :: V)) (gl G)", "  rw [phi2_one]\n")
    # A phase of a one-unit step
    th("zq_unit", "(t h : Nat) (G : List Nat) (L : Tape)", steps_of(raw, "aph_unit"),
       "(zc L (List.replicate t 2 ++ (h + 3) :: G))",
       "⟨rep (t + 2) [true, true, true] (cons false L), cons false (gl (h :: G)), .B⟩",
       "aph_unit t L (gl (h :: G))")
    th("zq_unit_blank", "(t : Nat) (L : Tape)", steps_of(raw, "aph_unit_blank"),
       "(zc L (List.replicate t 2))", "⟨rep (t + 2) [true, true, true] (cons false L), cons false (gl []), .B⟩",
       "aph_unit_blank t L")
    # anomalies
    new = "(List.replicate c 1 ++ [2])"
    th("qa_one", "(a c : Nat) (G : List Nat)", steps_of(raw, "anom_one"), "(qr [2 * c + 2] (a + 1) G)",
       f"(qr {new} 1 ((3 * a) :: G))", "anom_one a c (gl G)")
    th("qa_two", "(a c : Nat) (G : List Nat)", steps_of(raw, "anom_two"), "(qr [1, 2 * c + 2] (a + 2) G)",
       f"(qr (3 :: {new}) 1 ((3 * a + 1) :: G))", "anom_two a c (gl G)")
    if m == "1RB0RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_0LC---":
        th("qa_unit0", "(c h : Nat) (G : List Nat)", steps_of(raw, "anom_unit0_gap"),
           "(qr [1, 2 * c + 2] 1 ((h + 3) :: G))", f"(qr (5 :: {new}) 1 (h :: G))", "anom_unit0_gap c h (gl G)")
        th("qa_unit0_blank", "(c : Nat)", steps_of(raw, "anom_unit0_blank"), "(qr [1, 2 * c + 2] 1 [])",
           f"(qr (5 :: {new}) 1 [])", "anom_unit0_blank c")
        th("qa_units", "(c h t : Nat) (G : List Nat)", steps_of(raw, "anom_units_gap"),
           "(qr [1, 2 * c + 2] 1 (List.replicate (t + 1) 2 ++ (h + 3) :: G))", f"(qr (5 :: {new}) (t + 2) (h :: G))",
           "anom_units_gap c h t (gl G)")
        th("qa_units_blank", "(c t : Nat)", steps_of(raw, "anom_units_blank"),
           "(qr [1, 2 * c + 2] 1 (List.replicate (t + 1) 2))", f"(qr (5 :: {new}) (t + 2) [])",
           "anom_units_blank c t")
    # collisions
    ones = "List.replicate (3 * s) 1"
    for (tp, g, U), (C, ap, d) in TABLES[m].items():
        crev = " :: ".join(str(c) for c in reversed(C)) + " :: " + ones
        T = "2 * s" if tp == 0 else "2 * s + 1"
        Ul = {"0": "0", "1": "1", "2": "2"}.get(U, U.replace("+", " + "))
        ap_l = ap.replace("+", " + ")
        for tail in ("gap", "blank"):
            rname = f"coll_{'e' if tp == 0 else 'o'}{g}_{U.replace('+', '')}_{tail}"
            vs = sorted({"s"} | ({"h"} if tail == "gap" else set()) | ({"u"} if "u" in U else set()))
            G_in = f"List.replicate ({T}) 2 ++ {g} :: (List.replicate ({Ul}) 2 ++ " + \
                ("(h + 5) :: G)" if tail == "gap" else "[])")
            G_out = (f"((h + {d}) :: G)" if d else "(h :: G)") if tail == "gap" else "[]"
            binders = f"({' '.join(vs)} : Nat)" + (" (G : List Nat)" if tail == "gap" else "") + " (L : Tape)"
            call = f"{rname} {' '.join(vs)} L" + (" (gl G)" if tail == "gap" else "")
            th("z" + rname, binders, steps_of(raw, rname), f"(zc L ({G_in}))",
               f"⟨rep ({ap_l}) [true, true, true] (cons false (wlx ({crev}) (cons true (cons true L)))), "
               f"cons false (gl {G_out}), .B⟩", call)
    doc = (f"The rules of {m} restated on `qr` and `zc` (Abstract.lean).  Generated by `py/gen_collideq.py` in the "
           "folder of 1RB0RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_0LC---; do not edit by hand.")
    print(f"import Abstract\n\n/-! {doc} -/\n\nset_option linter.unusedSimpArgs false\n\nnamespace {ns}\n\nopen TM\n\n" + "\n".join(lem) + "\n" +
          "\n".join(ths) + f"\nend {ns}\n", end="")


if __name__ == "__main__":
    main()
