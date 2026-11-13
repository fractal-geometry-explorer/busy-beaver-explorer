"""The non-halting proof of 1RB0LE_1RC---_1RD1RE_1LA0RF_0RC0LA_0LC0RB: an invariant on the phase forms that every
move of the branch table preserves.

usage: python3 holdouts/1RB0LE_1RC---_1RD1RE_1LA0RF_0RC0LA_0LC0RB/py/closed.py     writes lean/Closed.lean
                                                                                   (needs lean/Table.lean)

The moves.  From each phase form the run goes, through one cycle iterate and one exit rule, to the next phase form
(`mv_*` below, 20 cases in all): the count that the cycle uses up is split by its residue (`S1`, `T2`, `U3` by c mod
2, `T3` by d mod 5) and the right phases by the parity of their run (`RF`, `RG`, `RG3`).  `O` is two forms here:
`O a 0 c` (after `rende`) and `O a b c` with b large (after `gend`).

The invariant `Good`.  For each of the ten forms a conjunction of linear inequalities in its counts (`INV` below):
  - homogeneous ones, `w . P >= 0` on the counts that grow: the ratios of the counts stay in a polyhedral cone,
    which every move maps strictly inside the cone of the next form (with room to spare, so the constant parts of
    the moves do not matter once the counts are large);
  - the bounded counts (`RF` k in {4,5}, `RG`/`RG3` n in {4,5}, `T3` a, x, y) and the exact relations of `T3`
    (x = 2a+4), `U3` (x - 2a in [0,2], 4y - 7a in [-13,27]) and `RG3` (4y + 21x - 49a in [-63,19]);
  - a size bound, `sigma(P) >= N` with sigma a positive linear form that every move multiplies by at least 1.1.
Lean proves (`good_step`) that from a Good configuration the machine makes at least one step and reaches a Good
configuration again: each case is one `mv_*` lemma plus `omega` on the inequalities.  The end of `table_from_blank`
is Good (`decide`), so the run from blank tape is defined for every length.

How the inequalities were found (not needed to check them): the forms' parameters along the replay, normalized,
give one cone per form; a fixpoint of linear programs over the moves' homogeneous parts (with a margin of 10^-3)
enlarges them to cones that the moves map strictly inside each other; a second linear program finds sigma.
Scratch scripts, using scipy; the result is the data below, and Lean checks it.
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "..", "..", "..", "tools", "py"))

NS = "H113677"
PARAMS = {"Op": "abc", "O0": "ac", "S1": "abc", "RF": "akm", "EF": "aq", "T3": "axdyzc", "T2": "axyc",
          "U3": "axyzc", "RG": "axnm", "RG3": "axynm"}
FORM = {"Op": "O", "O0": "O", "S1": "S1", "RF": "RF", "EF": "EF", "T3": "T3", "T2": "T2", "U3": "U3",
        "RG": "RG", "RG3": "RG3"}
ORDER = ["Op", "O0", "S1", "RF", "EF", "T3", "T2", "U3", "RG", "RG3"]
# each string: a linear form in the counts, with integer coefficients, that is >= 0 on Good configurations
INV = {
    "Op": [
        "+1321a -534b +321c +0",
        "+111a -131b +369c +0",
        "+631a +38b -369c +0",
        "-532a +483b -517c +0",
        "-895a +564b -436c +0",
        "-483a +211b +17c +0",
        "-850a +339b +150c +0",
        "+851a -149b -149c +0",
        "-17a -17b +108c +0",
        "+71b -50000000",
    ],
    "O0": [
        "+133a -67c +0",
        "-567a +433c +0",
        "+183c -100000000",
    ],
    "S1": [
        "+1322a -533b +322c +0",
        "+674a +3b -326c +0",
        "-283a +76b +217c +0",
        "+223a -261b +739c +0",
        "+213a -37b -37c +0",
        "-27a -27b +173c +0",
        "+1b -7",
        "+110a +75b +202c -100000000",
    ],
    "RF": [
        "+399a -101m +0",
        "-29a +11m +0",
        "+1k -4",
        "-1k +5",
        "+44a +25m -50000000",
    ],
    "EF": [
        "+133a -67q +0",
        "-567a +433q +0",
        "+99q -50000000",
    ],
    "T3": [
        "+661d -266z +161c +0",
        "+673d +2z -327c +0",
        "-566d +151z +434c +0",
        "+111d -131z +369c +0",
        "+851d -149z -149c +0",
        "-17d -17z +108c +0",
        "+1x -6",
        "+1y -8",
        "-1x +14",
        "-1y +15",
        "+1z -7",
        "+1x -2a -4",
        "-1x +2a +4",
        "-4y +7a +37",
        "+50d +77z +218c -100000000",
    ],
    "T2": [
        "+1001a -266x +1y +1c +0",
        "-887a +469x -175y +113c +0",
        "+23a -149x +122y +351c +0",
        "+522a +7x +359y -478c +0",
        "+667a -423x +970y -30c +0",
        "+764a -501x +1029y +29c +0",
        "+617a +38x +32y -383c +0",
        "+641a +37x -3y -359c +0",
        "-853a +382x -123y +147c +0",
        "-757a +292x -84y +243c +0",
        "-247a +19x +35y +253c +0",
        "-999a +430x +83y +1c +0",
        "-37a +88x -37y -37c +0",
        "-69a -69x +931y -69c +0",
        "-3a -3x -3y +197c +0",
        "+75x +31y +392c -100000000",
    ],
    "U3": [
        "-609a +137z +391c +0",
        "+338a +1z -162c +0",
        "-999a +801z +1c +0",
        "+230a -49z +30c +0",
        "+979a -262z +738c +0",
        "+889a -111z -111c +0",
        "-36a +89z -36c +0",
        "-13a -13z +487c +0",
        "+1x -2a +0",
        "-1x +2a +2",
        "+4y -7a +13",
        "-4y +7a +27",
        "+82a +85z +240c -100000000",
    ],
    "RG": [
        "+285a -116x +35m +0",
        "+347a -416x +584m +0",
        "-1157a +722x -278m +0",
        "-983a +427x +17m +0",
        "+776a +41x -224m +0",
        "-729a +652x -348m +0",
        "-919a +365x +81m +0",
        "+177a -23x -23m +0",
        "-79a +121x -79m +0",
        "-241a -241x +759m +0",
        "+1n -4",
        "-1n +5",
        "+129x -100000000",
    ],
    "RG3": [
        "+103a -10x -22m +0",
        "-485a +211x +15m +0",
        "+953a -363x -47m +0",
        "+1000a -441x +0",
        "+557a -554x +446m +0",
        "+427a -73x -73m +0",
        "-303a +697x -303m +0",
        "-319a -319x +681m +0",
        "+1n -4",
        "-1n +5",
        "+4y +21x -49a +63",
        "-4y -21x +49a +19",
        "+169m -100000000",
    ],
}


def parse(s):
    terms = re.findall(r"([+-]\d+)([a-z]?)", s)
    co, k = {}, 0
    for c, v in terms:
        if v:
            co[v] = co.get(v, 0) + int(c)
        else:
            k += int(c)
    return co, k


def ineq(s):
    co, k = parse(s)
    pos = [(f"{c} * {v}" if c != 1 else v) for v, c in co.items() if c > 0]
    neg = [(f"{-c} * {v}" if c != -1 else v) for v, c in co.items() if c < 0]
    if k > 0:
        pos.append(str(k))
    if k < 0:
        neg.append(str(-k))
    return f"{' + '.join(neg) or '0'} ≤ {' + '.join(pos) or '0'}"


def holds(nd, P):
    env = dict(zip(PARAMS[nd], P))
    for s in INV[nd]:
        co, k = parse(s)
        if k + sum(c * env[v] for v, c in co.items()) < 0:
            return False
    return True


def lhs(nd, vs):
    if nd == "O0":
        return f"O {vs[0]} 0 {vs[1]}"
    return f"{FORM[nd]} " + " ".join(vs)


HEAD = """/-- From a step count that is positive, the same run as one of the form `n + 1`. -/
theorem succ_of {m : Nat} {c c' : Config} (h : steps m c = some c') (hm : 0 < m) :
    ∃ n, steps (n + 1) c = some c' := ⟨m - 1, by rw [Nat.sub_add_cancel hm]; exact h⟩

theorem rf_odd (a q m : Nat) : RF a (2 * q + 1) m = RF2 a q m := by
  simp only [RF, RF2, rep_succ, rep_double]
  rfl

theorem rg_even (a x q m : Nat) : RG a x (2 * q) m = RG2 a x q m := by
  simp only [RG, RG2, rep_double, List.cons_append, List.nil_append]

theorem rg3_even (a x y q m : Nat) : RG3 a x y (2 * q) m = RG3p a x y q m := by
  simp only [RG3, RG3p, rep_double, List.cons_append, List.nil_append]

/-! ## The moves: one cycle iterate and one exit rule each -/

theorem mv_oentry (a b c : Nat) : ∃ n, steps (n + 1) (O a (b + 6) (c + 2)) = some (S1 (a + 1) (b + 6) c) :=
  succ_of (oentry a b c) (by omega)

theorem mv_ozero (a c : Nat) : ∃ n, steps (n + 1) (O a 0 (c + 3)) = some (S1 (a + 2) 7 c) := by
  have h := ozero a c
  rw [t3_s1] at h
  exact succ_of h (by omega)

theorem mv_s1even (a b k : Nat) :
    ∃ n, steps (n + 1) (S1 a (b + 6) (2 * k)) = some (RF (a + 3 * k + 3) 4 (b + 12 * k + 13)) := by
  obtain ⟨n1, h1⟩ := cycle_iter k a (b + 4) 0
  rw [show b + 4 + 2 + 12 * k = b + 12 * k + 3 + 3 by omega] at h1
  have h := steps_seq trans h1 (sexit0 (a + 3 * k) (b + 12 * k + 3))
  rw [show b + 4 + 2 = b + 6 by omega, show 0 + 2 * k = 2 * k by omega,
    show b + 12 * k + 3 + 10 = b + 12 * k + 13 by omega] at h
  exact succ_of h (by omega)

theorem mv_s1odd (a b k : Nat) :
    ∃ n, steps (n + 1) (S1 a (b + 6) (2 * k + 1)) = some (RF (a + 3 * k + 3) 5 (b + 12 * k + 12)) := by
  obtain ⟨n1, h1⟩ := cycle_iter k a (b + 4) 1
  rw [show b + 4 + 2 + 12 * k = b + 12 * k + 6 by omega] at h1
  have h := steps_seq trans h1 (oexit (a + 3 * k) (b + 12 * k))
  rw [show b + 4 + 2 = b + 6 by omega, show 1 + 2 * k = 2 * k + 1 by omega] at h
  exact succ_of h (by omega)

theorem mv_rfodd (a k m q : Nat) (hq : k + m = 2 * q + 1) :
    ∃ n, steps (n + 1) (RF a k (m + 1)) = some (EF a q) := by
  obtain ⟨n1, h1⟩ := rcyc_iter m a k 0
  rw [hq, show 0 + 1 + m = m + 1 by omega, show (0 : Nat) + 1 = 1 from rfl, rf_odd] at h1
  exact succ_of (steps_seq trans h1 (rend a q)) (by omega)

theorem mv_rfeven (a k m q : Nat) (hq : k + m = 2 * q) :
    ∃ n, steps (n + 1) (RF a k (m + 1)) = some (O a 0 (q + 1)) := by
  obtain ⟨n1, h1⟩ := rcyc_iter m a k 0
  rw [hq, show 0 + 1 + m = m + 1 by omega, show (0 : Nat) + 1 = 1 from rfl, rf_even] at h1
  exact succ_of (steps_seq trans h1 (rende a q)) (by omega)

theorem mv_eentry (a q : Nat) : ∃ n, steps (n + 1) (EF (a + 7) (q + 5)) = some (T3 5 14 a 8 7 (q + 2)) :=
  succ_of (eentry a q) (by omega)

theorem mv_texit0 (a x y z c k : Nat) :
    ∃ n, steps (n + 1) (T3 a (x + 6) (5 * k) (y + 6) (z + 6) (c + 2 * k + 1)) =
      some (T2 (a + 4 * k + 1) (x + y + 15 * k + 11) (z + 5 * k + 10) (c + 1)) := by
  obtain ⟨n1, h1⟩ := cycle3_iter k a x 0 y z (c + 1)
  rw [show x + 6 + 8 * k = x + 8 * k + 1 + 5 by omega, show y + 6 + 7 * k = y + 7 * k + 4 + 2 by omega,
    show z + 6 + 5 * k = z + 5 * k + 4 + 2 by omega] at h1
  have h := steps_seq trans h1 (texit0 (a + 4 * k) c (x + 8 * k + 1) (y + 7 * k + 4) (z + 5 * k + 4))
  rw [show 0 + 5 * k = 5 * k by omega, show c + 1 + 2 * k = c + 2 * k + 1 by omega,
    show x + 8 * k + 1 + (y + 7 * k + 4) + 6 = x + y + 15 * k + 11 by omega,
    show z + 5 * k + 4 + 6 = z + 5 * k + 10 by omega] at h
  exact succ_of h (by omega)

theorem mv_texit1 (a x y z c k : Nat) :
    ∃ n, steps (n + 1) (T3 a (x + 6) (5 * k + 1) (y + 6) (z + 6) (c + 2 * k + 2)) =
      some (U3 (a + 4 * k + 2) (x + 8 * k + 6) (y + 7 * k + 7) (z + 5 * k + 11) c) := by
  obtain ⟨n1, h1⟩ := cycle3_iter k a x 1 y z (c + 2)
  rw [show x + 6 + 8 * k = x + 8 * k + 6 by omega, show y + 6 + 7 * k = y + 7 * k + 1 + 5 by omega,
    show z + 6 + 5 * k = z + 5 * k + 6 by omega] at h1
  have h := steps_seq trans h1 (texit1 (a + 4 * k) c (x + 8 * k) (y + 7 * k + 1) (z + 5 * k))
  rw [show 1 + 5 * k = 5 * k + 1 by omega, show c + 2 + 2 * k = c + 2 * k + 2 by omega,
    show y + 7 * k + 1 + 6 = y + 7 * k + 7 by omega] at h
  exact succ_of h (by omega)

theorem mv_texit2 (a x y z c k : Nat) :
    ∃ n, steps (n + 1) (T3 a (x + 6) (5 * k + 2) (y + 6) (z + 6) (c + 2 * k + 2)) =
      some (U3 (a + 4 * k + 2) (x + 8 * k + 8) (y + 7 * k + 7) (z + 5 * k + 11) c) := by
  obtain ⟨n1, h1⟩ := cycle3_iter k a x 2 y z (c + 2)
  rw [show x + 6 + 8 * k = x + 8 * k + 6 by omega, show y + 6 + 7 * k = y + 7 * k + 1 + 5 by omega,
    show z + 6 + 5 * k = z + 5 * k + 6 by omega] at h1
  have h := steps_seq trans h1 (texit2 (a + 4 * k) c (x + 8 * k) (y + 7 * k + 1) (z + 5 * k))
  rw [show 2 + 5 * k = 5 * k + 2 by omega, show c + 2 + 2 * k = c + 2 * k + 2 by omega,
    show y + 7 * k + 1 + 6 = y + 7 * k + 7 by omega] at h
  exact succ_of h (by omega)

theorem mv_texit3 (a x y z c k : Nat) :
    ∃ n, steps (n + 1) (T3 a (x + 6) (5 * k + 3) (y + 6) (z + 6) (c + 2 * k + 3)) =
      some (T2 (a + 4 * k + 5) (x + y + 15 * k + 22) (z + 5 * k + 15) (c + 1)) := by
  obtain ⟨n1, h1⟩ := cycle3_iter k a x 3 y z (c + 3)
  rw [show x + 6 + 8 * k = x + 8 * k + 6 by omega, show y + 6 + 7 * k = y + 7 * k + 1 + 5 by omega,
    show z + 6 + 5 * k = z + 5 * k + 6 by omega] at h1
  have h := steps_seq trans h1 (texit3 (a + 4 * k) c (x + 8 * k) (y + 7 * k + 1) (z + 5 * k))
  rw [show 3 + 5 * k = 5 * k + 3 by omega, show c + 3 + 2 * k = c + 2 * k + 3 by omega,
    show x + 8 * k + (y + 7 * k + 1) + 21 = x + y + 15 * k + 22 by omega] at h
  exact succ_of h (by omega)

theorem mv_texit4 (a x y z c k : Nat) :
    ∃ n, steps (n + 1) (T3 a (x + 6) (5 * k + 4) (y + 6) (z + 6) (c + 2 * k + 3)) =
      some (T2 (a + 4 * k + 5) (x + y + 15 * k + 24) (z + 5 * k + 15) (c + 1)) := by
  obtain ⟨n1, h1⟩ := cycle3_iter k a x 4 y z (c + 3)
  rw [show x + 6 + 8 * k = x + 8 * k + 6 by omega, show y + 6 + 7 * k = y + 7 * k + 1 + 5 by omega,
    show z + 6 + 5 * k = z + 5 * k + 6 by omega] at h1
  have h := steps_seq trans h1 (texit4 (a + 4 * k) c (x + 8 * k) (y + 7 * k + 1) (z + 5 * k))
  rw [show 4 + 5 * k = 5 * k + 4 by omega, show c + 3 + 2 * k = c + 2 * k + 3 by omega,
    show x + 8 * k + (y + 7 * k + 1) + 23 = x + y + 15 * k + 24 by omega] at h
  exact succ_of h (by omega)

theorem mv_t2even (a x y k : Nat) :
    ∃ n, steps (n + 1) (T2 a (x + 6) (y + 10) (2 * k)) = some (RG (a + 3 * k + 3) (x + 7 * k + 5) 4 (y + 5 * k + 6)) := by
  obtain ⟨n1, h1⟩ := cycle2_iter k a x (y + 4) 0
  rw [show x + 6 + 7 * k = x + 7 * k + 4 + 2 by omega, show y + 4 + 6 + 5 * k = y + 5 * k + 10 by omega] at h1
  have h := steps_seq trans h1 (t2exit0 (a + 3 * k) (x + 7 * k + 4) (y + 5 * k))
  rw [show y + 4 + 6 = y + 10 by omega, show 0 + 2 * k = 2 * k by omega,
    show x + 7 * k + 4 + 1 = x + 7 * k + 5 by omega] at h
  exact succ_of h (by omega)

theorem mv_t2odd (a x y k : Nat) :
    ∃ n, steps (n + 1) (T2 a (x + 6) (y + 12) (2 * k + 1)) = some (RG (a + 3 * k + 3) (x + 7 * k + 5) 5 (y + 5 * k + 7)) := by
  obtain ⟨n1, h1⟩ := cycle2_iter k a x (y + 6) 1
  rw [show x + 6 + 7 * k = x + 7 * k + 4 + 2 by omega, show y + 6 + 6 + 5 * k = y + 5 * k + 12 by omega] at h1
  have h := steps_seq trans h1 (t2exit1 (a + 3 * k) (x + 7 * k + 4) (y + 5 * k))
  rw [show y + 6 + 6 = y + 12 by omega, show 1 + 2 * k = 2 * k + 1 by omega,
    show x + 7 * k + 4 + 1 = x + 7 * k + 5 by omega] at h
  exact succ_of h (by omega)

theorem mv_u3even (a x y z k : Nat) :
    ∃ n, steps (n + 1) (U3 a (x + 2) (y + 6) (z + 10) (2 * k)) =
      some (RG3 (a + 3 * k + 3) (x + 7 * k + 7) (y + 4) 4 (z + 5 * k + 10)) := by
  obtain ⟨n1, h1⟩ := ucyc_iter k a x y (z + 4) 0
  rw [show x + 2 + 7 * k = x + 7 * k + 2 by omega, show z + 4 + 6 + 5 * k = z + 5 * k + 10 by omega] at h1
  have h := steps_seq trans h1 (uexit0 (a + 3 * k) (x + 7 * k) y (z + 5 * k))
  rw [show z + 4 + 6 = z + 10 by omega, show 0 + 2 * k = 2 * k by omega] at h
  exact succ_of h (by omega)

theorem mv_u3odd (a x y z k : Nat) :
    ∃ n, steps (n + 1) (U3 a (x + 2) (y + 6) (z + 12) (2 * k + 1)) =
      some (RG3 (a + 3 * k + 3) (x + 7 * k + 7) (y + 4) 5 (z + 5 * k + 11)) := by
  obtain ⟨n1, h1⟩ := ucyc_iter k a x y (z + 6) 1
  rw [show x + 2 + 7 * k = x + 7 * k + 2 by omega, show z + 6 + 6 + 5 * k = z + 5 * k + 12 by omega] at h1
  have h := steps_seq trans h1 (uexit1 (a + 3 * k) (x + 7 * k) y (z + 5 * k))
  rw [show z + 6 + 6 = z + 12 by omega, show 1 + 2 * k = 2 * k + 1 by omega] at h
  exact succ_of h (by omega)

theorem mv_rgeven (a x n m q : Nat) (hq : n + m = 2 * q) :
    ∃ s, steps (s + 1) (RG (a + 2) x n (m + 1)) = some (O (a + 1) (x + 9) (q + 1)) := by
  obtain ⟨n1, h1⟩ := gcyc_iter m (a + 2) x n 0
  rw [hq, show 0 + 1 + m = m + 1 by omega, show (0 : Nat) + 1 = 1 from rfl, rg_even] at h1
  exact succ_of (steps_seq trans h1 (gend a q x)) (by omega)

theorem mv_rgodd (a x n m q : Nat) (hq : n + m = 2 * q + 7) :
    ∃ s, steps (s + 1) (RG (a + 3) (x + 6) n (m + 1)) = some (T3 1 6 a 11 (x + 14) (q + 1)) := by
  obtain ⟨n1, h1⟩ := gcyc_iter m (a + 3) (x + 6) n 0
  rw [hq, show 0 + 1 + m = m + 1 by omega, show (0 : Nat) + 1 = 1 from rfl,
    show 2 * q + 7 = 2 * (q + 3) + 1 by omega, rg_odd] at h1
  exact succ_of (steps_seq trans h1 (gendo a q x)) (by omega)

theorem mv_rg3even (a x y n m q : Nat) (hq : n + m = 2 * q + 4) :
    ∃ s, steps (s + 1) (RG3 a x (y + 4) n (m + 1)) = some (T2 (a + 3) (x + 9) (y + 10) (q + 1)) := by
  obtain ⟨n1, h1⟩ := g3cyc_iter m a x (y + 4) n 0
  rw [hq, show 0 + 1 + m = m + 1 by omega, show (0 : Nat) + 1 = 1 from rfl,
    show 2 * q + 4 = 2 * (q + 2) by omega, rg3_even] at h1
  exact succ_of (steps_seq trans h1 (g3end a q x y)) (by omega)

theorem mv_rg3odd (a x y n m q : Nat) (hq : n + m = 2 * q + 7) :
    ∃ s, steps (s + 1) (RG3 (a + 7) (x + 10) (y + 2) n (m + 1)) = some (T3 5 14 a 15 (x + y + 17) (q + 1)) := by
  obtain ⟨n1, h1⟩ := g3cyc_iter m (a + 7) (x + 10) (y + 2) n 0
  rw [hq, show 0 + 1 + m = m + 1 by omega, show (0 : Nat) + 1 = 1 from rfl,
    show 2 * q + 7 = 2 * (q + 3) + 1 by omega, rg3_odd] at h1
  exact succ_of (steps_seq trans h1 (g3endo a q x y)) (by omega)
"""

# node proofs: (node, body); `G(nd)` is replaced by the Good introduction of node nd
NODES = {
    "Op": """  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 6 := ⟨b - 6, by omega⟩
  obtain ⟨c', rfl⟩ : ∃ c', c = c' + 2 := ⟨c - 2, by omega⟩
  obtain ⟨n, hn⟩ := mv_oentry a b' c'
  exact ⟨n, _, hn, good_S1 (by unfold gS1; omega)⟩""",
    "O0": """  obtain ⟨c', rfl⟩ : ∃ c', c = c' + 3 := ⟨c - 3, by omega⟩
  obtain ⟨n, hn⟩ := mv_ozero a c'
  exact ⟨n, _, hn, good_S1 (by unfold gS1; omega)⟩""",
    "S1": """  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 6 := ⟨b - 6, by omega⟩
  obtain ⟨k, hk | hk⟩ : ∃ k, c = 2 * k ∨ c = 2 * k + 1 := ⟨c / 2, by omega⟩ <;> subst hk
  · obtain ⟨n, hn⟩ := mv_s1even a b' k
    exact ⟨n, _, hn, good_RF (by unfold gRF; omega)⟩
  · obtain ⟨n, hn⟩ := mv_s1odd a b' k
    exact ⟨n, _, hn, good_RF (by unfold gRF; omega)⟩""",
    "RF": """  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain ⟨q, hq | hq⟩ : ∃ q, k + m' = 2 * q + 1 ∨ k + m' = 2 * q := ⟨(k + m') / 2, by omega⟩
  · obtain ⟨n, hn⟩ := mv_rfodd a k m' q hq
    exact ⟨n, _, hn, good_EF (by unfold gEF; omega)⟩
  · obtain ⟨n, hn⟩ := mv_rfeven a k m' q hq
    exact ⟨n, _, hn, good_O0 (by unfold gO0; omega)⟩""",
    "EF": """  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 7 := ⟨a - 7, by omega⟩
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 5 := ⟨q - 5, by omega⟩
  obtain ⟨n, hn⟩ := mv_eentry a' q'
  exact ⟨n, _, hn, good_T3 (by unfold gT3; omega)⟩""",
    "T3": """  obtain ⟨x', rfl⟩ : ∃ x', x = x' + 6 := ⟨x - 6, by omega⟩
  obtain ⟨y', rfl⟩ : ∃ y', y = y' + 6 := ⟨y - 6, by omega⟩
  obtain ⟨z', rfl⟩ : ∃ z', z = z' + 6 := ⟨z - 6, by omega⟩
  obtain ⟨k, hk | hk | hk | hk | hk⟩ : ∃ k, d = 5 * k ∨ d = 5 * k + 1 ∨ d = 5 * k + 2 ∨ d = 5 * k + 3 ∨
      d = 5 * k + 4 := ⟨d / 5, by omega⟩ <;> subst hk
  · obtain ⟨c', rfl⟩ : ∃ c', c = c' + 2 * k + 1 := ⟨c - 2 * k - 1, by omega⟩
    obtain ⟨n, hn⟩ := mv_texit0 a x' y' z' c' k
    exact ⟨n, _, hn, good_T2 (by unfold gT2; omega)⟩
  · obtain ⟨c', rfl⟩ : ∃ c', c = c' + 2 * k + 2 := ⟨c - 2 * k - 2, by omega⟩
    obtain ⟨n, hn⟩ := mv_texit1 a x' y' z' c' k
    exact ⟨n, _, hn, good_U3 (by unfold gU3; omega)⟩
  · obtain ⟨c', rfl⟩ : ∃ c', c = c' + 2 * k + 2 := ⟨c - 2 * k - 2, by omega⟩
    obtain ⟨n, hn⟩ := mv_texit2 a x' y' z' c' k
    exact ⟨n, _, hn, good_U3 (by unfold gU3; omega)⟩
  · obtain ⟨c', rfl⟩ : ∃ c', c = c' + 2 * k + 3 := ⟨c - 2 * k - 3, by omega⟩
    obtain ⟨n, hn⟩ := mv_texit3 a x' y' z' c' k
    exact ⟨n, _, hn, good_T2 (by unfold gT2; omega)⟩
  · obtain ⟨c', rfl⟩ : ∃ c', c = c' + 2 * k + 3 := ⟨c - 2 * k - 3, by omega⟩
    obtain ⟨n, hn⟩ := mv_texit4 a x' y' z' c' k
    exact ⟨n, _, hn, good_T2 (by unfold gT2; omega)⟩""",
    "T2": """  obtain ⟨x', rfl⟩ : ∃ x', x = x' + 6 := ⟨x - 6, by omega⟩
  obtain ⟨k, hk | hk⟩ : ∃ k, c = 2 * k ∨ c = 2 * k + 1 := ⟨c / 2, by omega⟩ <;> subst hk
  · obtain ⟨y', rfl⟩ : ∃ y', y = y' + 10 := ⟨y - 10, by omega⟩
    obtain ⟨n, hn⟩ := mv_t2even a x' y' k
    exact ⟨n, _, hn, good_RG (by unfold gRG; omega)⟩
  · obtain ⟨y', rfl⟩ : ∃ y', y = y' + 12 := ⟨y - 12, by omega⟩
    obtain ⟨n, hn⟩ := mv_t2odd a x' y' k
    exact ⟨n, _, hn, good_RG (by unfold gRG; omega)⟩""",
    "U3": """  obtain ⟨x', rfl⟩ : ∃ x', x = x' + 2 := ⟨x - 2, by omega⟩
  obtain ⟨y', rfl⟩ : ∃ y', y = y' + 6 := ⟨y - 6, by omega⟩
  obtain ⟨k, hk | hk⟩ : ∃ k, c = 2 * k ∨ c = 2 * k + 1 := ⟨c / 2, by omega⟩ <;> subst hk
  · obtain ⟨z', rfl⟩ : ∃ z', z = z' + 10 := ⟨z - 10, by omega⟩
    obtain ⟨n, hn⟩ := mv_u3even a x' y' z' k
    exact ⟨n, _, hn, good_RG3 (by unfold gRG3; omega)⟩
  · obtain ⟨z', rfl⟩ : ∃ z', z = z' + 12 := ⟨z - 12, by omega⟩
    obtain ⟨n, hn⟩ := mv_u3odd a x' y' z' k
    exact ⟨n, _, hn, good_RG3 (by unfold gRG3; omega)⟩""",
    "RG": """  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain ⟨q, hq | hq⟩ : ∃ q, n + m' = 2 * q ∨ n + m' = 2 * q + 7 :=
    if h2 : (n + m') % 2 = 0 then ⟨(n + m') / 2, by omega⟩ else ⟨(n + m' - 7) / 2, by omega⟩
  · obtain ⟨a', rfl⟩ : ∃ a', a = a' + 2 := ⟨a - 2, by omega⟩
    obtain ⟨s, hs⟩ := mv_rgeven a' x n m' q hq
    exact ⟨s, _, hs, good_Op (by unfold gOp; omega)⟩
  · obtain ⟨a', rfl⟩ : ∃ a', a = a' + 3 := ⟨a - 3, by omega⟩
    obtain ⟨x', rfl⟩ : ∃ x', x = x' + 6 := ⟨x - 6, by omega⟩
    obtain ⟨s, hs⟩ := mv_rgodd a' x' n m' q hq
    exact ⟨s, _, hs, good_T3 (by unfold gT3; omega)⟩""",
    "RG3": """  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain ⟨q, hq | hq⟩ : ∃ q, n + m' = 2 * q + 4 ∨ n + m' = 2 * q + 7 :=
    if h2 : (n + m') % 2 = 0 then ⟨(n + m' - 4) / 2, by omega⟩ else ⟨(n + m' - 7) / 2, by omega⟩
  · obtain ⟨y', rfl⟩ : ∃ y', y = y' + 4 := ⟨y - 4, by omega⟩
    obtain ⟨s, hs⟩ := mv_rg3even a x y' n m' q hq
    exact ⟨s, _, hs, good_T2 (by unfold gT2; omega)⟩
  · obtain ⟨a', rfl⟩ : ∃ a', a = a' + 7 := ⟨a - 7, by omega⟩
    obtain ⟨x', rfl⟩ : ∃ x', x = x' + 10 := ⟨x - 10, by omega⟩
    obtain ⟨y', rfl⟩ : ∃ y', y = y' + 2 := ⟨y - 2, by omega⟩
    obtain ⟨s, hs⟩ := mv_rg3odd a' x' y' n m' q hq
    exact ⟨s, _, hs, good_T3 (by unfold gT3; omega)⟩""",
}


def main():
    with open(os.path.join(HERE, "..", "lean", "Table.lean")) as fh:
        m = re.search(r"theorem table_from_blank : ∃ n, steps n init = some \((\w+) ([\d ]+)\)", fh.read())
    f, P = m.group(1), [int(v) for v in m.group(2).split()]
    end = ("O0" if P[1] == 0 else "Op") if f == "O" else f
    if end == "O0":
        P = [P[0], P[2]]
    assert holds(end, P), f"the end of Table.lean, {f} {P}, does not satisfy the invariant: choose another bound"
    out = []
    for nd in ORDER:
        vs = list(PARAMS[nd])
        out.append(f"/-- The invariant at `{lhs(nd, vs)}`. -/\ndef g{nd} ({' '.join(vs)} : Nat) : Prop :=\n  "
                   + " ∧\n  ".join(ineq(s) for s in INV[nd]) + "\n")
    disj = []
    for nd in ORDER:
        vs = list(PARAMS[nd])
        disj.append(f"(∃ {' '.join(vs)}, t = {lhs(nd, vs)} ∧ g{nd} {' '.join(vs)})")
    out.append("/-- A configuration at a phase form whose counts satisfy the invariant. -/\n"
               "def Good (t : Config) : Prop :=\n  " + " ∨\n  ".join(disj) + "\n")
    for i, nd in enumerate(ORDER):
        vs = list(PARAMS[nd])
        pre = "Or.inr (" * i
        post = ")" * i
        inner = f"⟨{', '.join(vs)}, rfl, h⟩"
        term = f"{pre}Or.inl {inner}{post}" if i < len(ORDER) - 1 else f"{'Or.inr (' * (i - 1)}Or.inr {inner}{')' * (i - 1)}"
        out.append(f"theorem good_{nd} {{{' '.join(vs)} : Nat}} (h : g{nd} {' '.join(vs)}) : Good ({lhs(nd, vs)}) :=\n"
                   f"  {term}\n")
    for nd in ORDER:
        vs = list(PARAMS[nd])
        out.append(f"/-- From the form `{lhs(nd, vs)}` with the invariant, the next form with the invariant. -/\n"
                   f"theorem step_{nd} ({' '.join(vs)} : Nat) (h : g{nd} {' '.join(vs)}) :\n"
                   f"    ∃ i t', steps (i + 1) ({lhs(nd, vs)}) = some t' ∧ Good t' := by\n"
                   f"  unfold g{nd} at h\n" + NODES[nd] + "\n")
    pats = " | ".join(f"⟨{', '.join(PARAMS[nd])}, rfl, h⟩" for nd in ORDER)
    out.append(f"""/-- The invariant is restored after at least one step. -/
theorem good_step (t : Config) (h : Good t) : ∃ n t', steps (n + 1) t = some t' ∧ Good t' := by
  rcases h with {pats}
""" + "\n".join(f"  · exact step_{nd} {' '.join(PARAMS[nd])} h" for nd in ORDER) + "\n")
    last = lhs(end, list(map(str, P)))
    out.append(f"""/-- The end of `table_from_blank` satisfies the invariant. -/
theorem good_last : Good ({last}) := good_{end} (by unfold g{end}; decide)

/-- From blank tape the machine never halts. -/
theorem nonhalting : ¬ HaltsFromBlank := by
  obtain ⟨n0, h0⟩ := table_from_blank
  apply not_halts_of_forall
  apply forall_of_unbounded trans (fun m => ∃ c, steps m init = some c ∧ Good c)
  · intro N
    induction N with
    | zero => exact ⟨n0, Nat.zero_le _, _, h0, good_last⟩
    | succ N ih =>
      obtain ⟨m, hm, c, h1, h2⟩ := ih
      obtain ⟨n, c', h3, h4⟩ := good_step c h2
      exact ⟨m + (n + 1), by omega, c', steps_seq trans h1 h3, h4⟩
  · rintro m ⟨c, h, -⟩
    exact ⟨c, h⟩
""")
    text = f"""import Table

/-! # It never halts

`Good` (an invariant on the phase forms: linear inequalities in their counts) holds at the end of
`table_from_blank`, and `good_step` restores it after at least one step, through the moves `mv_*` (one cycle
iterate and one exit rule of `Cycle.lean`, `Phase.lean`, `Branch.lean`, `Ends.lean` each).  So the run from blank
tape is defined for every length (`nonhalting`).

Generated by `py/closed.py`. -/

namespace {NS}

open TM

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

""" + HEAD + "\n/-! ## The invariant -/\n\n" + "\n".join(out) + f"\nend {NS}\n"
    with open(os.path.join(HERE, "..", "lean", "Closed.lean"), "w") as fh:
        fh.write(text)


if __name__ == "__main__":
    main()
