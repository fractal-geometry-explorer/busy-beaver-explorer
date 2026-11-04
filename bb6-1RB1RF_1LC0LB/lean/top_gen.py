"""Generate Top.lean: the top pieces of `py/top.py` (listed in top_shapes.txt), each proved along its symbolic run
(`tools/py/bbtools/symtm.py`) and composed with the counter's walk and sweep (`counter_borrow_any` in Counter.lean)
into a whole trip from the right end and back.

usage: python3 top_gen.py > Top.lean      (tests/test_machine.py checks that the committed file is current)

For each shape i:
* `top_piece_i`: the raw run, as `symtm.prove` writes it;
* `top_i`: the whole trip, with the tape written as blocks: a block of n pairs `10` is `rep n P`, the seps are
  `cons`, as in `lv`.  For a piece after a walk (`turn`), the levels the walk crosses are any list `zs` with the last
  level `(2c+2, 2d+2)` in front, exactly as in `counter_borrow1`; for a piece that is the whole trip (`last`) the
  statement is the trip.  The left of the piece is blank tape (it reaches the left end) or any tape `L`.
The tape equalities between the two writings are closed by `simp` with the rewriting lemmas of Counter.lean.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "py"))
import top  # noqa: E402
from bbtools.symtm import Blank, Config, Ctx, Lin, left_term, lin, prove  # noqa: E402

B = {"0": "false", "1": "true"}
NF = "simp only [rep_add, rq, rep_succ, rep_zero, app_cons, app_nil, pq, rotf, F3]"


def term(bl):
    """A left tape from blocks (left to right): `rep n P` for a block, `cons` for a sep."""
    acc = None
    for t in bl:
        if isinstance(t, Blank):
            acc = "blank"
        elif isinstance(t, Ctx):
            acc = t.name
        elif isinstance(t, Lin):
            if not t.is_zero():
                acc = f"rep ({t.lean()}) P ({acc})"
        else:
            acc = f"cons {B[t]} ({acc})"
    return acc


def plus2(bl):
    """The piece's tape with the two pairs the walk took given back to its last block."""
    bl = list(bl)
    if isinstance(bl[-1], Lin):
        bl[-1] = bl[-1] + 2
    else:
        bl.append(lin(2))
    return bl


def unsummed(raw):
    """`prove` states the step count in closed form and checks the sum with `omega`, which is slow on long runs;
    state it as the sum of the segments instead, which the chain of `steps_seq` has by definition."""
    lines = raw.rstrip("\n").split("\n")
    last = lines[-1]
    pre = "  exact steps_congr trans (a := "
    assert last.startswith(pre), last
    i = len(pre)
    depth = 1
    j = i
    while depth:
        depth += {"(": 1, ")": -1}.get(last[j], 0)
        j += 1
    total = last[i:j - 1]
    rest = last[j:]
    assert rest.startswith(" (by omega) "), rest[:20]
    lines[-1] = "  exact " + rest[len(" (by omega) "):]
    k = next(n for n, ln in enumerate(lines) if ln.startswith("    steps ("))
    head = lines[k]
    depth, a = 1, len("    steps (")
    b = a
    while depth:
        depth += {"(": 1, ")": -1}.get(head[b], 0)
        b += 1
    lines[k] = head[:a] + total + head[b - 1:]
    return "\n".join(lines) + "\n", total


def theorem(i, start):
    sh = top.Shape(start)
    cfg = Config.parse(start)
    fin = top.run_piece(start, sh.turn)
    name = f"top_piece_{i}"
    raw, _ = prove(top.M, name, cfg, fin, doc=f"The run of top piece {i} ({sh}).")
    raw, total = unsummed(raw)
    vs = sorted(cfg.vars() | fin.vars())            # the binder order of `prove`
    ctxs = []
    for x in cfg.contexts() + fin.contexts():
        if x not in ctxs:
            ctxs.append(x)
    has_l = "L" in ctxs
    binders = (f" ({' '.join(sh.vars)} : Nat)" if sh.vars else "")
    args = " ".join(vs)
    rawT, rawE = left_term(cfg.left), left_term(fin.left)
    lines = [raw]
    if sh.turn:
        start_t, end_t = term(plus2(sh.lhs)), term(sh.rhs)
        lines.append(f"/-- Top piece {i} after a borrow: {sh}. -/")
        lines.append(f"theorem top_{i}{binders} (c d : Nat) (zs : List (Nat × Nat)){' (L : Tape)' if has_l else ''} :")
        lines.append(f"    ∃ n, steps n ⟨lv false false (2 * c + 2) (2 * d + 2) (Zs zs ({start_t})), R0, .C⟩")
        lines.append(f"      = some ⟨lv true true (2 * c + 3) (2 * d + 3) (Rs zs ({end_t})), R0, .C⟩ := by")
        lines.append(f"  have e1 : {start_t} = app Q ({rawT}) := by {NF}")
        lines.append(f"  have h : ∀ R : Tape, steps ({total}) ⟨{rawT}, W5 (cons false (cons true R)), .C⟩"
                     f" = some ⟨F3 ({end_t}), R, .C⟩ := by")
        lines.append("    intro R")
        lines.append(f"    have h := {name} {args} {'L ' if has_l else ''}R")
        lines.append(f"    have e2 : {rawE} = F3 ({end_t}) := by {NF}")
        lines.append("    rw [e2] at h; exact h")
        lines.append("  rw [e1]; exact counter_borrow_any c d zs h ⟨_, rfl⟩")
    else:
        start_t, end_t = term(sh.lhs), term(sh.rhs)
        lines.append(f"/-- Top piece {i}, a whole trip: {sh}. -/")
        lines.append(f"theorem top_{i}{binders}{' (L : Tape)' if has_l else ''} :")
        lines.append(f"    ∃ n, steps n ⟨{start_t}, R0, .C⟩ = some ⟨{end_t}, R0, .C⟩ := by")
        lines.append(f"  have e1 : {start_t} = {rawT} := by {NF}")
        lines.append(f"  have e2 : {rawE} = {end_t} := by {NF}")
        lines.append(f"  have h := {name} {args}{' L' if has_l else ''}")
        lines.append("  rw [e1, ← e2]; exact ⟨_, h⟩")
    return "\n".join(lines) + "\n"


HEAD = """import Counter

/-! # The top of the counter

Generated by `top_gen.py` from the shapes in `top_shapes.txt` (found by `py/top.py shapes`); do not edit by hand.

The trips from the right end that `Counter.lean` does not cover end at the left end of the tape or at a level of
the wrong parity.  Each such trip is the counter's walk over standard digit-0 levels, then a *top piece*, then the
counter's sweep back; or, when the last level is not standard, a piece that is the whole trip.  For every piece
seen in the run to 10^11 steps there is a theorem here: `top_piece_i`, the run itself, and `top_i`, the whole trip
with the tape written as blocks of pairs (`rep n P`) and seps.  Lengths are variables wherever the run does not
depend on them.  Kernel only. -/

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace BB6e

open TM

"""


def main():
    out = [HEAD]
    for i, st in enumerate(top.load_shapes()):
        out.append(theorem(i, st))
    out.append("end BB6e\n")
    sys.stdout.write("\n".join(out))


if __name__ == "__main__":
    main()
