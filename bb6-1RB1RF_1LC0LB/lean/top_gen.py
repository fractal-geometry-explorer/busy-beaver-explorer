"""Generate Top.lean: the top pieces of `py/top.py` (listed in top_shapes.txt), each proved along its symbolic run
(`tools/py/bbtools/symtm.py`) and composed with the counter's walk and sweep (`counter_borrow_any` in Counter.lean)
into a whole trip from the right end and back.

usage: python3 top_gen.py      writes Top.lean, TopWall*.lean and AxiomsWall.lean (tests/test_machine.py checks that they are current)

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
import family  # noqa: E402
import top  # noqa: E402
import wall  # noqa: E402
from bbtools import seqtm  # noqa: E402
from bbtools.symtm import Blank, Config, Ctx, Lin, Rep, left_term, lin, prove, right_term  # noqa: E402

B = {"0": "false", "1": "true"}
NF = "simp only [rep_add, rq, rep_succ, rep_zero, app_cons, app_nil, pq, rotf, F3]"


def count(n):
    """A block length in Lean.  Lengths like `4 * x + 7` are written `2 * (2 * x) + 7`, so that `rq` turns their
    pairs into the `(0101)^m` of the symbolic runs."""
    if any(a > 2 for a in n.c.values()) and all(a % 2 == 0 for a in n.c.values()):
        half = Lin(0, {v: a // 2 for v, a in n.c.items()})
        return f"2 * ({half.lean()})" + (f" + {n.k}" if n.k else "")
    return n.lean()


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
                acc = f"rep ({count(t)}) P ({acc})"
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


NF_WALL = f"first | ({NF}; done) | {NF[:-1]}, rep_swap]"
NFW = ("simp only [Rd, WBs, WB, WX, rep_add, rep_succ, rep_zero, app_cons, app_nil, rpq, rpq0, mv10, mv01, mvQ, "
       "mvQ0]")


def binders_of(c1, c2):
    """The variables and contexts of a `prove` theorem from c1 to c2, in its binder order."""
    vs = sorted(c1.vars() | c2.vars())
    ctxs = []
    for x in c1.contexts() + c2.contexts():
        if x not in ctxs:
            ctxs.append(x)
    return vs, ctxs


def abstract(a, b):
    """The stretch from a to b with each count `V + k` whose variable part V has two or more variables or a
    coefficient above 1, or whose constant k is large, written `y + (k - k0)` for a fresh variable y = V + k0 (k0 the
    smallest constant with that V).  Lean's kernel is slow on such counts in long runs; the theorem applied to
    y := V + k0 is the stretch.  Returns the two configurations and {y: V + k0}."""
    def reps(c):
        return [t for t in c.left + c.right if isinstance(t, Rep)]

    k0 = {}
    for t in reps(a) + reps(b):
        if t.n.c:
            key = tuple(sorted(t.n.c.items()))
            k0[key] = min(k0.get(key, t.n.k), t.n.k)
    names, ys = {}, {}
    for key, k in k0.items():
        if len(key) > 1 or key[0][1] > 1 or k >= 4:
            names[key] = f"y{len(names)}"
            ys[names[key]] = Lin(k, dict(key))

    def lin2(n):
        key = tuple(sorted(n.c.items()))
        if key not in names:
            return n
        return Lin(n.k - k0[key], {names[key]: 1})

    def toks(ts):
        return [Rep(t.word, lin2(t.n)) if isinstance(t, Rep) else t for t in ts]

    def cfg(c):
        return Config(toks(c.left), c.state, toks(c.right), c.steps)

    return cfg(a), cfg(b), ys


def inst(text, ys):
    """Lean text of an abstracted stretch with its fresh variables replaced by what they stand for."""
    import re
    return re.sub(r"\by\d+\b", lambda m: f"({ys[m.group(0)].lean()})" if m.group(0) in ys else m.group(0), text)


def wall_piece(i, sh, doc):
    """A piece whose run jumps over copy loops (`wall.py`): the plain stretches proved by `prove`, the loops by
    `wall_jump` (Wall.lean), the tapes between the two writings matched by `simp`.  States `∃ n`."""
    out, name, k = [], f"top_piece_{i}", 0
    calls = []
    for part in sh.jumps:
        if isinstance(part, wall.Jump):
            calls.append(part)
            continue
        a, b = part
        pname = f"{name}_{k}"
        a2, b2, ys = abstract(a, b)
        raw, _ = prove(top.M, pname, a2, b2, doc=f"Top piece {i}, stretch {k}.")
        raw, _ = unsummed(raw)
        out.append(raw)
        vs, ctxs = binders_of(a2, b2)
        args = [f"({ys[v].lean()})" if v in ys else v for v in vs]
        calls.append((pname, " ".join(args + ctxs), a2, b2, ys, a, b))
        k += 1
    first, last = calls[0], calls[-1]
    vs, ctxs = binders_of(first[5], last[6])
    binders = (f" ({' '.join(vs)} : Nat)" if vs else "") + (f" ({' '.join(ctxs)} : Tape)" if ctxs else "")
    a0, b0 = first[2], last[3]
    start_l, start_r = inst(left_term(a0.left), first[4]), inst(right_term(a0.right), first[4])
    end_l, end_r = inst(left_term(b0.left), last[4]), inst(right_term(b0.right), last[4])
    lines = [f"/-- {doc} -/", f"theorem {name}{binders} :",
             f"    ∃ n, steps n ⟨{start_l}, {start_r}, .{'ABCDEF'[a0.state]}⟩"
             f" = some ⟨{end_l}, {end_r}, .{'ABCDEF'[b0.state]}⟩ := by"]
    hs = []
    for j, c in enumerate(calls):
        if isinstance(c, wall.Jump):
            r = c.rnd
            ts = "[" + ", ".join(f"{t.lean()}" for t in r.ts) + "]"
            rt = right_term(r.rest)
            prev = calls[j - 1]
            lines.append(f"  rw [show {inst(right_term(prev[3].right), prev[4])} = Rd ({r.a.lean()}) {ts} ({r.X.lean()}) ({rt}) by")
            lines.append(f"    {NFW}] at h{j - 1}")
            lines.append(f"  obtain ⟨m{j}, h{j}⟩ := wall_jump ({r.a.lean()}) {ts} ({r.X.lean()}) ({rt})")
            ax = (r.a + r.X).lean()
            if ax != f"{r.a.lean()} + {r.X.lean()}" or len(r.X.c) + (r.X.k != 0) > 1:
                lines.append(f"  rw [show {r.a.lean()} + ({r.X.lean()}) = {ax} by omega] at h{j}")
            nxt = calls[j + 1]
            lines.append(f"  rw [show Rd ({ax}) {ts} 0 ({rt}) = {inst(right_term(nxt[2].right), nxt[4])} by")
            lines.append(f"    {NFW}] at h{j}")
        else:
            lines.append(f"  have h{j} := {c[0]} {c[1]}")
        hs.append(f"h{j}")
    chain = hs[-1]
    for h in reversed(hs[:-1]):
        chain = f"steps_seq trans {h} ({chain})"
    lines.append(f"  exact ⟨_, {chain}⟩")
    out.append("\n".join(lines) + "\n")
    return "\n".join(out), (start_l, end_l, vs, ctxs)


def theorem(i, start):
    sh = top.Shape(start)
    if sh.wall:
        return wall_theorem(i, start, sh)
    cfg = Config.parse(start)
    fin = top.run_piece(start, sh.turn, walls=False)
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


def wall_theorem(i, start, sh):
    """`top_i` for a piece that builds a wall: as `theorem`, with the piece stated `∃ n` (`counter_borrow_ex`)."""
    cfg = Config.parse(start)
    raw, (rawT, rawE, vs, ctxs) = wall_piece(i, sh, f"The run of top piece {i} ({sh}), copy loops jumped over by "
                                                    "`wall_jump`.")
    name = f"top_piece_{i}"
    has_l = "L" in ctxs
    binders = (f" ({' '.join(sh.vars)} : Nat)" if sh.vars else "")
    args = " ".join(vs)
    lines = [raw]
    if sh.turn:
        start_t, end_t = term(plus2(sh.lhs)), term(sh.rhs)
        lines.append(f"/-- Top piece {i} after a borrow, building a wall: {sh}. -/")
        lines.append(f"theorem top_{i}{binders} (c d : Nat) (zs : List (Nat × Nat)){' (L : Tape)' if has_l else ''} :")
        lines.append(f"    ∃ n, steps n ⟨lv false false (2 * c + 2) (2 * d + 2) (Zs zs ({start_t})), R0, .C⟩")
        lines.append(f"      = some ⟨lv true true (2 * c + 3) (2 * d + 3) (Rs zs ({end_t})), R0, .C⟩ := by")
        lines.append(f"  have e1 : {start_t} = app Q ({rawT}) := by {NF_WALL}")
        lines.append(f"  have h : ∀ R : Tape, ∃ m, steps m ⟨{rawT}, W5 (cons false (cons true R)), .C⟩"
                     f" = some ⟨F3 ({end_t}), R, .C⟩ := by")
        lines.append("    intro R")
        lines.append(f"    obtain ⟨m, h⟩ := {name} {args} {'L ' if has_l else ''}R")
        lines.append(f"    have e2 : {rawE} = F3 ({end_t}) := by {NF_WALL}")
        lines.append("    rw [e2] at h; exact ⟨m, h⟩")
        lines.append("  rw [e1]; exact counter_borrow_ex c d zs h ⟨_, rfl⟩")
    else:
        start_t, end_t = term(sh.lhs), term(sh.rhs)
        lines.append(f"/-- Top piece {i}, a whole trip building a wall: {sh}. -/")
        lines.append(f"theorem top_{i}{binders}{' (L : Tape)' if has_l else ''} :")
        lines.append(f"    ∃ n, steps n ⟨{start_t}, R0, .C⟩ = some ⟨{end_t}, R0, .C⟩ := by")
        lines.append(f"  have e1 : {start_t} = {rawT} := by {NF_WALL}")
        lines.append(f"  have e2 : {rawE} = {end_t} := by {NF_WALL}")
        lines.append(f"  have h := {name} {args}{' L' if has_l else ''}")
        lines.append("  rw [e1, ← e2]; exact h")
    return "\n".join(lines) + "\n"


def family_theorem(i, text):
    """`fam_piece_i`, the run of family i (`bbtools.seqtm`: every list crossed at once by induction), and `fam_i`,
    the whole trip, after a borrow (with `counter_borrow_ex`) or on its own."""
    f = family.Family(text)
    name = f"fam_piece_{i}"
    raw, fin, _ = seqtm.prove(top.M, name, f.cfg, top._at_end(f.turn), doc=f"The run of family {i}: `{text}`.")
    lists, vs = seqtm.seq_vars(f.cfg)
    _, vs2 = seqtm.seq_vars(fin)
    vs = sorted(vs | vs2)
    ctxs = [c for c in dict.fromkeys(f.cfg.contexts() + fin.contexts())]
    seqs = {t.name: t for t in f.cfg.left if isinstance(t, seqtm.Seq)}
    binders = (f" ({' '.join(vs)} : Nat)" if vs else "")
    binders += "".join(f" ({n} : List ({seqtm.ptype(s.params)}))" for n, s in seqs.items())
    has_l = "L" in ctxs
    args = " ".join(vs + list(seqs))
    rawT = seqtm.left_term(f.cfg.left)
    lines = [raw]
    if f.turn:
        tail = fin.left[-4:]
        if tail != [0, 1, 1, 0]:
            raise ValueError(f"family {i} does not end with `0 1 1 0` left of the head: {fin}")
        X = seqtm.left_term(fin.left[:-3])
        lines.append(f"/-- Family {i} after a borrow: `{text}`. -/")
        lines.append(f"theorem fam_{i}{binders} (c d : Nat) (zs : List (Nat × Nat)){' (L : Tape)' if has_l else ''} :")
        lines.append(f"    ∃ n, steps n ⟨lv false false (2 * c + 2) (2 * d + 2) (Zs zs (app Q ({rawT}))), R0, .C⟩")
        lines.append(f"      = some ⟨lv true true (2 * c + 3) (2 * d + 3) (Rs zs ({X})), R0, .C⟩ :=")
        lines.append(f"  counter_borrow_ex c d zs (fun R => {name} {args} {'L ' if has_l else ''}R) ⟨_, rfl⟩")
    else:
        rawE = seqtm.left_term(fin.left)
        lines.append(f"/-- Family {i}, a whole trip: `{text}`. -/")
        lines.append(f"theorem fam_{i}{binders}{' (L : Tape)' if has_l else ''} :")
        lines.append(f"    ∃ n, steps n ⟨{rawT}, R0, .C⟩ = some ⟨{rawE}, R0, .C⟩ :=")
        lines.append(f"  {name} {args}{' L' if has_l else ''}")
    return "\n".join(lines) + "\n"


FAM_HEAD = """import Wall
import Seq

/-! # The top of the counter: families of shapes

Generated by `top_gen.py` from the families in `top_families.txt` (found by `py/family.py find`); do not edit by
hand.  A family is a top shape with a list of blocks of any length (`sq f ts` on the tape): its run crosses the
whole list at once each time the head meets it, by induction on the list (`seqL`, `seqR`, `seqL'`, `seqR'` of
`Seq.lean`, each with the run of one block, `fam_piece_i_bk`).  `fam_i` is the whole trip from the right end and
back, for every list and every value of the variables.  Kernel only. -/

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace BB6e

open TM

"""


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


WALL_HEAD = """import Wall

/-! # The top of the counter: trips that build a wall ({part})

Generated by `top_gen.py` from the shapes in `top_shapes.txt`; do not edit by hand.  As `Top.lean`, for the pieces
in which the head copies a level into a new first block: their runs are plain symbolic stretches (`top_piece_i_k`)
chained with the copy loop `wall_jump` of `Wall.lean`.  The pieces are split over several files to keep the memory
of one Lean process low.  Kernel only. -/

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace BB6e

open TM

"""
WALL_FILE_SIZE = 1_000_000      # characters of proof per TopWall file, roughly


def files():
    """{file name: content}: `Top.lean` with the plain pieces, `TopWall1.lean`, ... with the wall pieces, and
    `AxiomsWall.lean`, which prints the axioms of the wall pieces."""
    fams = [FAM_HEAD] + [family_theorem(i, t) for i, t in enumerate(family.load())] + ["end BB6e\n"]
    plain, walls, wall_ids = [HEAD], [[]], []
    for i, st in enumerate(top.load_shapes()):
        if top.Shape(st).wall:
            if sum(map(len, walls[-1])) > WALL_FILE_SIZE:
                walls.append([])
            walls[-1].append(theorem(i, st))
            wall_ids.append(i)
        else:
            plain.append(theorem(i, st))
    plain.append("end BB6e\n")
    out = {"Top.lean": "\n".join(plain), "TopFam.lean": "\n".join(fams)}
    for k, ths in enumerate(w for w in walls if w):
        out[f"TopWall{k + 1}.lean"] = "\n".join([WALL_HEAD.replace("{part}", f"part {k + 1}")] + ths + ["end BB6e\n"])
    n = len([w for w in walls if w])
    out["AxiomsWall.lean"] = "\n".join(
        [f"import TopWall{k + 1}" for k in range(n)]
        + ["", "/-! What the wall-building top pieces (TopWall*.lean) rest on, as Axioms.lean for the rest: "
               "`lean AxiomsWall.lean`", "prints the axioms. Generated by top_gen.py. -/", ""]
        + [f"#print axioms BB6e.top_{i}" for i in wall_ids]) + "\n"
    return out


def main():
    """Write the files next to this script."""
    for name, text in files().items():
        with open(os.path.join(HERE, name), "w") as f:
            f.write(text)


if __name__ == "__main__":
    main()
