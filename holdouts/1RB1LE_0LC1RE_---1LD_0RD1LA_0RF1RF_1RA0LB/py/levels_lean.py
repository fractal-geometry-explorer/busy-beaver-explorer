"""Writes lean/Levels.lean: the level rules of accel.py, proved by bbtools.symtm for every block count and every
tape to the left and to the right of the level.

A level `4^n s` occupies the cells  s' (0111111111)^n  (s' the separator in tape order).  A hit from above is a list
of calls: the head enters the level's rightmost cell from the right in a state.  Each call is cut into *stretches*
at the moments the head leaves the level:

  * to the right, onto the first cell of the tape R right of the level (the call returns to the front side), or
  * to the left: the stretch ends with the head on the level's leftmost cell, about to step onto the rest L
    (a call on the rest); the next stretch starts when that call has returned, the head on the same cell in the
    return state.

For every position p of the table and every stretch there is one theorem `lev<p>_<i>`, for all j (n = j + 1), L, R.
The generator checks while it runs that the states in which the head leaves are the ones of the call lists (SIG),
that a level at an absorbing position never touches L, and that after the last stretch the level is
`4^n' s'` with the next separator of the table, less its last pair (H-hit) or last three pairs (V-hit): these
are 1s that lie right of the level's old border and are written from above; in the same way a level that passes
a hit on leaves one pair (three pairs) of 1s at its left border to the rest.

usage: python3 levels_lean.py > ../lean/Levels.lean
"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../../tools/py"))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from bbtools.symtm import prove, rules_file, Config, Ctx, Rep, run, canon, lin, _unroll_back, _unroll_front
from bbtools.machine import Machine
from accel import CYC, PASS, INC, SEPW, SIG
from words import M, CELLS

NS = "H23376"
BLOCK = (0, 1, 1, 1, 1, 1, 1, 1, 1, 1)
m = Machine.parse(M)
ST = "ABCDEF"


def cells(word):
    """a word of pairs (read from the head leftwards) as cells in tape order"""
    out = []
    for ch in reversed(word):
        out.extend(CELLS[ch])
    return out


def expand(tks, j):
    out = []
    for t in tks:
        if isinstance(t, Rep):
            out.extend(list(t.word) * t.n.subs({"j": j}))
        else:
            out.append(t)
    return out


def calls(sig):
    return [(ST.index(sig[i + 1]), ST.index(sig[i + 3])) for i in range(0, len(sig), 4)]


def level(pos):
    s, t = CYC[pos]
    region = cells(SEPW[s]) + [Rep(BLOCK, lin("j"))] + list(BLOCK)
    out_calls = calls(SIG[PASS[pos]]) if pos in PASS else []
    thms, k_out, idx = [], 0, 0
    doc0 = "position %d (separator %s, %s-hit)" % (pos, s, t)
    for ci, (q_in, r_exp) in enumerate(calls(SIG[t])):
        cfg = Config([Ctx("L")] + region[:-1], q_in, [region[-1], Ctx("R")])
        what = "call %d from above (in %s)" % (ci + 1, ST[q_in])
        while True:
            start = cfg.copy()

            def stop(c):
                if c.right == [Ctx("R")]:
                    return True
                if c.left == [Ctx("L")]:
                    x = c.right[0]
                    x = x.word[0] if isinstance(x, Rep) else x
                    tr = m.table[c.state][x]
                    return tr is not None and tr[1] == -1
                return False
            try:
                fin = run(m, cfg, stop, rotate=True)
            except Exception as e:
                sys.stderr.write("pos %d call %d start %r now %r: %r\n" % (pos, ci, start, cfg, e))
                raise
            idx += 1
            name = "lev%d_%d" % (pos, idx)
            if fin.right == [Ctx("R")]:
                assert fin.state == r_exp, (pos, ci)
                doc = "%s, %s: to the return in %s." % (doc0, what, ST[fin.state])
                thms.append(prove(m, name, start, fin, doc=doc, rotate=True, count_first=True, max_seg=24)[0])
                region = fin.left[1:]
                _unroll_back(region)
                break
            rest = list(fin.right)
            _unroll_front(rest)
            w, d, q2 = m.table[fin.state][rest[0]]
            q_exp, r2 = out_calls[k_out]
            assert q2 == q_exp, (pos, ci, k_out)
            k_out += 1
            doc = ("%s, %s: to the head on the level's leftmost cell, about to write %d and step onto the rest in %s "
                   "(call %d on the rest)." % (doc0, what, w, ST[q2], k_out))
            if fin.steps.is_zero():
                idx -= 1               # the head steps back onto the rest at once: nothing to prove
            else:
                thms.append(prove(m, name, start, fin, doc=doc, rotate=True, count_first=True, max_seg=24)[0])
            cfg = Config([Ctx("L")], r2, [w] + rest[1:])
            what = "after call %d on the rest has returned (in %s)" % (k_out, ST[r2])
    assert k_out == len(out_calls), pos
    s2 = CYC[(pos + 1) % 16][0]
    grow = 2 if t == "H" else 6       # the level ends 1 or 3 pairs further right: 1s that the side above supplies
    give = 0 if pos not in PASS else 2 if PASS[pos] == "H" else 6      # pairs handed to the rest, in the same way
    want = cells(SEPW[s2]) + [Rep(BLOCK, lin("j") + (1 if pos in INC else 0))] + list(BLOCK)
    for j in range(4):
        assert expand(region, j)[give:] + [1] * grow == expand(want, j), (pos, region, want)
        assert expand(region, j)[:give] == [1] * give
    return thms


def last_visit():
    """the last visit on the reduced word: the front `2 1`, the tail `0 3 1 0 3 1 0 5`, blank tape to the left"""
    from bbtools.symtm import cfg_term
    word = "YYXYX" + "XYYYXYXXYYYXYXXYYYYY"
    tape = dict(enumerate(cells(word)))
    pos, st, n = len(tape), 0, 0
    start = "0^inf " + " ".join(map(str, cells(word))) + " A> 0^inf"
    while True:
        tr = m.table[st][tape.get(pos, 0)]
        if tr is None:
            break
        tape[pos], pos, st = tr[0], pos + tr[1], tr[2]
        n += 1
    lo, hi = min(min(tape), pos), max(max(tape), pos)
    end = ("0^inf " + " ".join(str(tape.get(p, 0)) for p in range(lo, pos)) + " " + ST[st] + "> " +
           " ".join(str(tape.get(p, 0)) for p in range(pos, hi + 1)) + " 0^inf")
    assert ST[st] == "C" and tape.get(pos, 0) == 0 and n == 278
    t, fin = prove(m, "last_visit_run", start, end, doc="The visit of the word `2 1  0 3 1 0 3 1 0 5` (the front and the "
                   "tail of the last visit of the accelerated run) with blank tape to its left: %d steps to C on a 0."
                   % n, cross=False, count_first=True, max_seg=24)
    return [t, "/-- The last visit on the reduced word halts: the head runs through the tail into the blank left end. -/\n"
            "theorem last_visit_halts : ∃ c, steps (%d) %s = some c ∧ step c = none :=\n"
            "  ⟨_, last_visit_run, rfl⟩\n" % (n, cfg_term(Config.parse(start)))]


def main():
    thms = []
    for pos in range(16):
        thms += level(pos)
    thms += last_visit()
    doc = ("The level rules: every stretch of a hit on a level `4^(j+1) s` between two crossings of its borders, "
           "for the 16 positions of the table in `py/accel.py`. Generated by `py/levels_lean.py`, which also checks "
           "that the stretches chain as the table says.")
    print(rules_file("Machine", NS + ".Levels", thms, doc), end="")
    sys.stderr.write("%d theorems\n" % len(thms))


if __name__ == "__main__":
    main()
