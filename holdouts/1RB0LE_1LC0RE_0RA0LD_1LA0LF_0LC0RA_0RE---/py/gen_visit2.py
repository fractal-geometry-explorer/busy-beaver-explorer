"""Write a Lean file of token-level visit laws (rows mined by vislaws.c), each a kernel-checked conditional theorem.

Adapted from py/gen_visit.py of holdouts/1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RA_0LB---, for streams on either side of
the head.  usage: gen_visit2.py MACHINE NAMESPACE SIDE ROWS.jsonl IMPORT MODULE_DOC_EXTRA STEPS > File.lean

SIDE R: `Vis q x r x'` (the stream x right of the cell the head comes from); SIDE L: `VisL q x r x'`, its mirror
image (the stream x left of that cell, nearest cell first).  Tokens are listed from the near side outward.
If IMPORT is the name of a file that already defines the predicate, pass DEFINE=0 in the environment.
"""
import sys, json, os


def parse(m):
    t = {}
    for i, s in enumerate(m.split('_')):
        for r in range(2):
            x = s[3 * r:3 * r + 3]
            if x[2] != '-':
                t[(i, r)] = (int(x[0]), 1 if x[1] == 'R' else -1, ord(x[2]) - 65)
    return t


S = "ABCDEF"
B = lambda v: "true" if v else "false"


def cons(cells, tail):
    for c in reversed(cells):
        tail = "cons %s (%s)" % (c, tail) if ' ' in tail else "cons %s %s" % (c, tail)
    return tail


def gen(m, ns, side, rows, imp, steps_desc, define=True):
    tr = parse(m)
    out = []
    P = "Vis" if side == "R" else "VisL"
    out.append(f"import {imp}\n")
    if define:
        out.append(f"""/-! # Visit laws of {m} ({'right' if side == 'R' else 'left'} side)

Every theorem below is one row of a token-level visit law (mined from the run by `py/vislaws.c`, written by
`py/gen_visit2.py`): what one visit does to a stream that starts with the token, given what the nested visits of the
rest of the stream do.  Rows are exact for every stream (the hypotheses are about the rest only). -/
""")
    out.append(f"namespace {ns}\n\nopen TM\n")
    if define and side == "R":
        out.append("""/-- One visit of the stream `x` (right of the head's cell) in state `q`: back out on the left in state `r`, leaving
`x'`; the cell it lands on and everything left of it are untouched. -/
def Vis (q : St) (x : Tape) (r : St) (x' : Tape) : Prop :=
  ∀ (a : Bool) (L : Tape), ∃ t, steps t ⟨cons a L, x, q⟩ = some ⟨L, cons a x', r⟩
""")
    if define and side == "L":
        out.append("""/-- One visit of the stream `x` (left of the head's cell, nearest cell first) in state `q`: the head steps onto `x 0`
and the first time it comes back out on the right it is in state `r`, the stream is `x'`, and the cell it lands on
and everything right of it are untouched. -/
def VisL (q : St) (x : Tape) (r : St) (x' : Tape) : Prop :=
  ∀ (a : Bool) (R : Tape), ∃ t, steps t ⟨tail x, cons (x 0) (cons a R), q⟩ = some ⟨x', cons a R, r⟩
""")
    out_dir = 1 if side == "R" else -1
    for q, tok, calls, r, tok2, cnt, first in rows:
        W = len(tok)
        cells = [int(c) for c in tok]
        cl = [(calls[i], calls[i + 1].upper()) for i in range(0, len(calls), 2)]
        st = S.index(q); pos = 0; k = 0; segs = []; j = 0; ok = True
        start = (list(cells), st, pos)
        while True:
            if pos == W:
                if j >= len(cl) or S[st] != cl[j][0]:
                    ok = False; break
                segs.append((start, k, list(cells), st, cl[j][1]))
                st = S.index(cl[j][1]); pos = W - 1; j += 1; k = 0; start = (list(cells), st, pos); continue
            if pos == -1:
                ok = (S[st] == r and "".join(map(str, cells)) == tok2 and j == len(cl)); break
            key = (st, cells[pos])
            if key not in tr:
                ok = False; break
            w, d, st = tr[key]; cells[pos] = w; pos += d * out_dir; k += 1
        assert ok, (q, tok, calls, r, tok2)
        name = f"{'v' if side == 'R' else 'w'}_{q}_{tok}_{calls or 'none'}"
        xs = ["x"] + [f"x{i + 1}" for i in range(len(cl))]
        hyps = " ".join(f"(h{i + 1} : {P} .{cl[i][0]} {xs[i]} .{cl[i][1]} {xs[i + 1]})" for i in range(len(cl)))
        L = []
        L.append(f"/-- `{q}` entering `{tok} x`" + (f", nested visits {' '.join(a + '→' + b for a, b in cl)}" if cl else ", no nested visit")
                 + f": out in state {r}, leaving `{tok2} x'`.  (In the run: {cnt} times in {steps_desc}, first at step {first}.) -/")
        L.append(f"theorem {name} {{{' '.join(xs)} : Tape}} {hyps} :\n    {P} .{q} ({cons([B(c) for c in [int(c) for c in tok]], 'x')}) .{r} ({cons([B(int(c)) for c in tok2], xs[-1])}) := by")
        L.append("  intro a " + ("L" if side == "R" else "R"))
        ctx = "cons a L" if side == "R" else "cons a R"

        def cfg(cs, s, p, xi):
            # configuration with head at token position p (0 = near cell), cells cs, rest stream xi
            if side == "R":
                left = cons([B(v) for v in reversed(cs[:p])], ctx)
                right = cons([B(v) for v in cs[p:]], xi)
                return f"⟨{left}, {right}, .{S[s]}⟩"
            else:
                right = cons([B(v) for v in reversed(cs[:p + 1])], ctx)
                left = cons([B(v) for v in cs[p + 1:]], xi)
                return f"⟨{left}, {right}, .{S[s]}⟩"

        def callcfg(cs, s, xi):
            if side == "R":
                return f"⟨{cons([B(v) for v in reversed(cs)], ctx)}, {xi}, .{S[s]}⟩"
            else:
                return f"⟨tail {xi}, cons ({xi} 0) ({cons([B(v) for v in reversed(cs)], ctx)}), .{S[s]}⟩"

        chain = []
        for i, (stt, kk, cend, qcall, ret) in enumerate(segs):
            c0, s0, p0 = stt
            L.append(f"  have s{i} : steps {kk} {cfg(c0, s0, p0, xs[i])} = some {callcfg(cend, qcall, xs[i])} := rfl")
            L.append(f"  obtain ⟨t{i + 1}, c{i + 1}⟩ := h{i + 1} {B(cend[-1])} ({cons([B(v) for v in reversed(cend[:-1])], ctx)})")
            chain += [f"s{i}", f"c{i + 1}"]
        c0, s0, p0 = start
        i = len(segs)
        endtok = cons([B(int(c)) for c in tok2], xs[-1])
        if side == "R":
            fin = f"⟨L, cons a ({endtok}), .{r}⟩"
        else:
            fin = f"⟨{endtok}, cons a R, .{r}⟩"
        L.append(f"  have s{i} : steps {k} {cfg(c0, s0, p0, xs[i])} = some {fin} := rfl")
        chain.append(f"s{i}")
        e = chain[-1]
        for c in reversed(chain[:-1]):
            e = f"steps_seq trans {c} ({e})"
        L.append(f"  exact ⟨_, {e}⟩\n")
        out.append("\n".join(L))
    out.append(f"end {ns}")
    return "\n".join(out)


if __name__ == "__main__":
    m, ns, side, rf, imp, steps_desc = sys.argv[1:7]
    rows = [json.loads(l) for l in open(rf) if l.strip()]
    rows.sort(key=lambda r: (r[0], r[1], r[2]))
    print(gen(m, ns, side, rows, imp, steps_desc, define=os.environ.get("DEFINE", "1") == "1"))
