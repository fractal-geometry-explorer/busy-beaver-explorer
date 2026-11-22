"""Visit rows for blocks of any length (the 2-cell rows of gen_visit.py, generalized).

A row: the head enters the block `cells` (followed by an arbitrary stream x) from the left in state q; each time it
leaves the block to the right it makes one nested visit of the rest of the stream, which comes back in the state
given; the row ends when the head leaves the block to the left.  row() simulates the block, checks the given exit
state and block contents, and returns the Lean theorem (proof: the step runs between the nested visits, by rfl)."""
import sys
S = "ABCDEF"

def table(m):
    t = {}
    for i, s in enumerate(m.split('_')):
        for r in range(2):
            x = s[3 * r:3 * r + 3]
            if x[2] != '-':
                t[(i, r)] = (int(x[0]), 1 if x[1] == 'R' else -1, ord(x[2]) - 65)
    return t

B = lambda v: "true" if v else "false"

def cons(cells, tail):
    for c in reversed(cells):
        tail = "cons %s (%s)" % (c, tail) if ' ' in tail else "cons %s %s" % (c, tail)
    return tail

def row(tr, name, q, block, calls, doc=""):
    """calls: list of (entry, exit) states of the nested visits, in order.  Returns (exit state, block after, lean)."""
    cells = [int(c) for c in block]; W = len(cells)
    st = S.index(q); pos = 0; k = 0; segs = []; j = 0
    start = (list(cells), st, 0)
    while True:
        if pos == W:
            assert j < len(calls) and S[st] == calls[j][0], (name, 'nested visit', j, S[st])
            segs.append((start, k, list(cells), st)); st = S.index(calls[j][1]); pos = W - 1; j += 1; k = 0
            start = (list(cells), st, 1); continue
        if pos == -1:
            break
        key = (st, cells[pos])
        assert key in tr, (name, 'halts')
        w, d, st = tr[key]; cells[pos] = w; pos += d; k += 1
    assert j == len(calls), (name, 'unused calls')
    r = S[st]; after = "".join(map(str, cells))
    xs = ["x"] + [f"x{i+1}" for i in range(len(calls))]
    hyps = " ".join(f"(h{i+1} : Vis .{calls[i][0]} {xs[i]} .{calls[i][1]} {xs[i+1]})" for i in range(len(calls)))
    L = [f"/-- `{q}> {block} x`" + (f", nested visits {' '.join(a + '→' + b for a, b in calls)}" if calls else ", no nested visit")
         + f": out in state {r}, leaving `{after} x'`. {doc} -/"]
    L.append(f"theorem {name} {{{' '.join(xs)} : Tape}} {hyps} :\n    Vis .{q} ({cons([B(int(c)) for c in block], 'x')}) .{r} ({cons([B(int(c)) for c in after], xs[-1])}) := by")
    L.append("  intro a L")
    def left(c):
        return cons([B(v) for v in reversed(c)], "cons a L")
    chain = []
    def src(i, c0, s0):
        if i == 0:
            return f"⟨cons a L, {cons([B(v) for v in c0], 'x')}, .{S[s0]}⟩"
        return f"⟨{cons([B(v) for v in reversed(c0[:-1])], 'cons a L')}, {cons([B(c0[-1])], xs[i])}, .{S[s0]}⟩"
    for i, ((c0, s0, _), kk, cend, qcall) in enumerate(segs):
        L.append(f"  have s{i} : steps {kk} {src(i, c0, s0)} = some ⟨{left(cend)}, {xs[i]}, .{S[qcall]}⟩ := rfl")
        L.append(f"  obtain ⟨t{i+1}, c{i+1}⟩ := h{i+1} {B(cend[-1])} ({cons([B(v) for v in reversed(cend[:-1])], 'cons a L')})")
        chain += [f"s{i}", f"c{i+1}"]
    c0, s0, _ = start; i = len(segs)
    L.append(f"  have s{i} : steps {k} {src(i, c0, s0)} = some ⟨L, cons a ({cons([B(int(c)) for c in after], xs[-1])}), .{r}⟩ := rfl")
    chain.append(f"s{i}")
    e = chain[-1]
    for c in reversed(chain[:-1]):
        e = f"steps_seq trans {c} ({e})"
    L.append(f"  exact ⟨_, {e}⟩\n")
    return r, after, "\n".join(L)
