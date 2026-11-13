"""Write lean/Instance.lean: the clock theorem of lean/Clock.lean applied to the real run from blank tape.

The tick theorem `tick_left_end j` holds for every word W that goes through 2^j P-steps (`PChain`).  This file shows
that its hypothesis is met by the words of the actual run: starting from the configuration `blank, J j0 W0, Y` that
the run from blank tape reaches at step t0 (checked by `decide` on the list simulator), every P-step of the next
`n` ticks is proved concretely (`bbtools.symtm.prove`, for every tape to the left and every tape beyond the cells it
reads), and `tick_left_end` then carries the run through the n ticks.  The result `run_ticks` is a statement about
the run from blank tape, proved through the clock theorem.

For a machine of `clock.MIRROR` everything is done on the mirror image (MirrorClock.lean), whose run from blank tape
is the mirror image of the machine's.

usage (from the repository root): python3 holdouts/1RB0LE_0LC0RB_1RD1LD_1RA1LF_0LB1LE_---1LB/py/instance.py M T0 N
  T0: a step at which the run (of the mirror image, for a MIRROR machine) is `blank, J j0 W0, Y`; N: ticks to cover.
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
CLK = os.path.join(ROOT, "holdouts", "1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE", "py")
sys.path.insert(0, os.path.join(ROOT, "tools", "py"))
sys.path.insert(0, CLK)
from bbtools.symtm import prove  # noqa: E402
import clock  # noqa: E402
from gen_clock import params  # noqa: E402


def lb(cells):
    return "[" + ", ".join("true" if c else "false" for c in cells) + "]"


def blank_run(T, t):
    """The list configuration of `TM.fsteps` after t steps from blank tape (left cells nearest first, right cells
    from the head, state), exactly as the list simulator of tools/lean/TM/Fin.lean builds it."""
    l, r, st = [], [], 0
    for _ in range(t):
        w, d, s = T[(st, r[0] if r else 0)]
        if d == 1:
            l, r = [w] + l, r[1:]
        else:
            l, r = l[1:], [l[0] if l else 0, w] + r[1:]
        st = s
    return l, r, st


def main(m, t0, n):
    X, Y, B0, g, h, A, s, Bp, PR, pz = params(m)
    mm = clock.mirror(m) if m in clock.MIRROR else m
    pre = "Mirror" if m in clock.MIRROR else ""
    d = os.path.join(ROOT, "holdouts", m, "lean")
    ns = re.search(r"^namespace (\w+)", open(os.path.join(d, pre + "Machine.lean")).read(), re.M).group(1)
    ck = clock.Clock(m)
    ck.nested = False
    C = ck.base + g                       # the C of Clock.lean (sweep + merge + g)
    Ys, Zs = "ABCDEF"[ck.Y], "ABCDEF"[ck.Z]
    left, right, st = blank_run(ck.T, t0)
    assert not any(left) and st == ck.Y, (left, st)
    assert h == 1, "head on the block"
    L = 0
    while L < len(right) and right[L] == 1:
        L += 1
    assert L >= B0 and (L - B0) % g == 0 and right[L:L + 1] in ([0], []), right[:L + 2]
    j0 = (L - B0) // g
    W = bytes(right[L + 1:])
    words, costs, reads, levels = [W], [], [], []
    for i in range(n):
        for _ in range(2 ** (j0 + i)):
            r = ck.P(W)
            assert r[0] != "abn", ("abnormal P-step", i)
            pre_w, rr, cost = r
            W = (pre_w + W[rr:]).rstrip(b"\0")
            words.append(W)
            costs.append(cost - ck.base)
            reads.append(rr)
            levels.append(i)
    N = max([len(w) for w in words] + reads)  # every word padded to N cells: the P-steps read only these
    pad = [list(w) + [0] * (N - len(w)) for w in words]
    lemmas = []
    lc = " ".join(["0"] * pz + [str(c) for c in Bp])
    pr = " ".join(map(str, ck.prc))
    for k in range(len(costs)):
        txt, fin = prove(mm, f"pstep{k}", f"L {lc} {Zs}> {pr} {' '.join(map(str, pad[k]))} R",
                         f"L {Ys}> {' '.join(['1'] * B0)} 0 {' '.join(map(str, pad[k + 1]))} R", max_seg=100,
                         doc=f"P-step {k} of the run (in tick {levels[k]}).")
        assert int(str(fin.steps)) == costs[k], (fin.steps, costs[k])
        lemmas.append(txt)
    defs = [f"def w{k} : List Bool := {lb(pad[k])}" for k in range(len(pad))]
    body = [f"""/-- The run from blank tape reaches `blank, J {j0} W, {Ys}` at step {t0} (list simulator, `decide`). -/
theorem at_start' : steps {t0} init = some ⟨blank, J {j0} (app {lb(right[L + 1:])} blank), .{Ys}⟩ :=
  blank_reaches trans (c := ⟨{lb(left)}, {lb(right)}, .{Ys}⟩) (by decide +kernel)

theorem at_start : steps {t0} init = some ⟨blank, J {j0} (app w0 blank), .{Ys}⟩ := by
  have e : app {lb(right[L + 1:])} blank = app w0 blank := by simp only [w0, app, cons_false_blank]
  rw [← e]; exact at_start'
"""]
    for k in range(len(costs)):
        body.append(f"theorem ps{k} : PStep (app w{k} blank) (app w{k + 1} blank) {costs[k]} := fun L => pstep{k} L blank\n")
    proof = ["  have h0 := at_start"]
    acc, k = t0, 0
    for i in range(n):
        j = j0 + i
        ks = list(range(k, k + 2 ** j))
        ch = "(.zero _)"
        for q in reversed(ks):
            ch = f"(.succ ps{q} {ch})"
        cnt = sum(costs[q] for q in ks) + C * 2 ** j - g
        body.append(f"""/-- Tick {i} of the run: level {j}, {2 ** j} P-steps, {cnt} steps (`tick_left_end`). -/
theorem tick{i} : steps {cnt} ⟨blank, J {j} (app w{ks[0]} blank), .{Ys}⟩ =
    some ⟨blank, J {j + 1} (app w{ks[-1] + 1} blank), .{Ys}⟩ :=
  steps_congr trans (by decide) (tick_left_end {j} _ _ _ {ch})
""")
        proof.append(f"  have h{i + 1} := steps_congr trans (show {acc} + {cnt} = {acc + cnt} by decide) "
                     f"(steps_seq trans h{i} tick{i})")
        acc += cnt
        k += 2 ** j
    proof.append(f"  exact h{n}")
    jl = j0 + n
    body.append(f"""/-- **The clock carries the real run**: from step {t0} the run from blank tape goes through {n} ticks of
`tick_left_end` (levels {j0} to {jl - 1}) and is at `blank, J {jl} W, {Ys}` at step {acc}. -/
theorem run_ticks : steps {acc} init = some ⟨blank, J {jl} (app w{k} blank), .{Ys}⟩ := by
""" + "\n".join(proof) + "\n")
    head = f'''import {pre}Clock

/-!
# The clock on the run from blank tape{' (mirror image)' if pre else ''}

Written by `holdouts/1RB0LE_0LC0RB_1RD1LD_1RA1LF_0LB1LE_---1LB/py/instance.py {m} {t0} {n}`.  The hypothesis of
`tick_left_end` (a chain of 2^j P-steps) is met by the words of the actual run: each P-step of the {n} ticks after
step {t0} is proved for every tape to the left (`pstepK`, by `bbtools.symtm.prove`), and `run_ticks` follows the run
from blank tape through those ticks with `tick_left_end`.  So the tick theorem is not vacuous: it is what the machine
does.
-/

set_option maxRecDepth 20000

namespace {ns}

open TM

'''
    out = head + "\n".join(defs) + "\n\n" + "\n".join(lemmas) + "\n\n" + "\n".join(body) + f"\nend {ns}\n"
    open(os.path.join(d, pre + "Instance.lean"), "w").write(out)
    cks = os.path.join(d, "check.sh")
    sh = open(cks).read()
    if pre + "Instance.lean" not in sh:
        open(cks, "w").write(sh.rstrip("\n") + f" {pre}Instance.lean\n")
    print("t0", t0, "j0", j0, "ticks", n, "end step", acc, "P-steps", len(costs), "cells", N)


if __name__ == "__main__":
    main(sys.argv[1], int(sys.argv[2]), int(sys.argv[3]))
