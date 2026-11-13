"""Writes lean/Start.lean: the run from blank tape to the first epoch (P1 59 0, step 638,914), by native_decide.

usage: python3 start.py > ../lean/Start.lean
"""
M = "1RB1RB_0LC0LD_0LE1LD_1LB0RE_1RA0RF_1RD---"
N = 638914
E = {"a": "10", "b": "100", "c": "1000"}
B = {0: "false", 1: "true"}


def w(t):
    return "".join(E[x] for x in t)


def main():
    T = {}
    for i, s in enumerate(M.split("_")):
        for b in range(2):
            t = s[3 * b:3 * b + 3]
            T["ABCDEF"[i], b] = None if t == "---" else (int(t[0]), 1 if t[1] == "R" else -1, t[2])
    tape, p, s = {}, 0, "A"
    for _ in range(N):
        wr, d, s = T[s, tape.get(p, 0)]
        tape[p] = wr
        p += d
    assert s == "D" and p > max(tape)
    left = [tape.get(i, 0) for i in range(p - 1, min(tape) - 1, -1)]       # nearest first
    part = [int(x) for x in reversed(w("baccaaa") * 59 + w("ba") + "1" + "00" + w("aaa") + w("caa") * 2 + w("c") + "1")]
    assert left[:len(part)] == part
    lst = lambda xs: "[" + ", ".join(B[x] for x in xs) + "]"
    print(TEMPLATE.format(L0=lst(left[len(part):]), LS=lst(left)), end="")


TEMPLATE = r'''import Phases

/-! # From blank tape to the first epoch, and through its first phase

`py/start.py` wrote the lists (the tape left of the head at step 638,914, nearest cell first). -/

namespace H181063

open TM

/-- The tape left of the first epoch's moving part (nearest cell first). -/
def L0 : List Bool := {L0}

/-- The whole tape left of the head at step 638,914. -/
def Lstart : List Bool := {LS}

set_option maxRecDepth 100000 in
/-- After 638,914 steps from blank tape the machine is at `P1 59 0`: the first epoch starts, with 59 copies of
`baccaaa` (T = 7, X = 6T + 17 = 59). Evaluated by compiled code (`native_decide`). -/
theorem blank_to_epoch0 : steps 638914 init = some (P1 59 0 (app L0 blank)) := by
  have h : fsteps 638914 (FCfg.blank St.A) = some ⟨Lstart, [], .D⟩ := by native_decide
  exact blank_reaches trans h

/-- From blank tape the machine reaches `P1 0 59`: the first phase of the first epoch runs to its end without a halt. -/
theorem blank_to_phase1_end : ∃ t, steps t init = some (P1 0 59 (app L0 blank)) := by
  obtain ⟨t, h⟩ := phase1 59 (app L0 blank)
  exact ⟨638914 + t, steps_seq trans blank_to_epoch0 h⟩

end H181063
'''

if __name__ == "__main__":
    main()
