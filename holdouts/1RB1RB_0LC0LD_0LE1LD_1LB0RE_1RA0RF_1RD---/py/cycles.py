"""The long cycles of phases 3 and 4, checked by exact symbolic simulation (bbtools.symtm) for every value of the counts.

Letters a = 10, b = 100, c = 1000, and U = (c)^7 (bac)^5 acacbacb (ac)^3 (bac)^5 aca (168 cells).  The two
configurations below are tapes of the run at visits 17,264 and 18,500 (epoch 4, T = 187; found by direct simulation,
the part right of (bac)^1119), with the head in state D on the first blank cell.  Every long run of a repeated word
becomes a variable (with an offset where it shrinks), the tape left of the cut is an unknown context L, and symtm
runs P visits, re-bracketing the tape between visits (py/tapeeq.py).  The check: the end configuration is the start
with every variable moved by its increment, for all values of the variables and every L (the run never looks at L).

  phase 3:  144 visits:  U +1, (acacaaac) +12, (acaaac) +72, (aac) -144
  phase 4:  288 visits:  U +1, (acaaacac) +12, (acaaac) -72, (acaaa) +144

This is an exact computation, not a Lean proof (the Lean terms symtm writes for these 144 and 288 visits run to
hundreds of megabytes).

usage: python3 cycles.py
"""
import os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import tapeeq
from bbtools import symtm

M = "1RB1RB_0LC0LD_0LE1LD_1LB0RE_1RA0RF_1RD---"
E = {"a": "10", "b": "100", "c": "1000"}
U = "ccccccc" + "bac" * 5 + "acacbacb" + "ac" * 3 + "bac" * 5 + "aca"
HEAD = ("cc (a)^17 cacb (ac)^3 babac (cba)^3 cacacbacb (ac)^3 bacbacaca (bac)^7 acacbacb (ac)^3 (bac)^5 aca ")
CYCLES = [
    ("phase 3", 144, {"U": "u", "acacaaac": "p", "acaaac": "q", "aac": "r"},
     HEAD + "(U)^3 (c)^13 bacb (ac)^3 bacb (ac)^3 (bac)^5 acacbacba (ac)^9 (bac)^3 ac (acb)^5 (ac)^3 bacb (ac)^4 a "
     "(ac)^5 (bac)^3 ac (acb)^5 (ac)^3 bacb (ac)^7 bac (cba)^3 cac (acb)^5 (ac)^3 bacb (ac)^7 (bac)^3 ba (bac)^4 aca "
     "(ac)^3 (bac)^3 (ac)^6 (bac)^10 b (a)^3 cacbac100acbacb (a)^9 (ca)^3 (ac)^3 cb (acacaaac)^127 acb (aacaacac)^3 "
     "aacaacbaccb (acaaac)^778 b (aac)^736 1"),
    ("phase 4", 288, {"U": "u", "acaaacac": "p", "acaaac": "q", "acaaa": "r"},
     HEAD + "(U)^10 (c)^13 bacb (ac)^3 bacb (ac)^3 (bac)^5 acacbacba (ac)^9 (bac)^3 ac (acb)^5 (ac)^3 bacb (ac)^4 a "
     "(ac)^5 (bac)^3 ac (acb)^5 (ac)^3 bacb (ac)^7 bac (cba)^3 cac (acb)^5 (ac)^3 bacb (ac)^7 (bac)^4 (c)^3 bacb "
     "(ac)^3 bac (cba)^3 (ca)^6 (cba)^13 (a)^7 caacacaacacba100acb (acaaacac)^209 ac (a)^3 cb (acaacaac)^3 "
     "acaacaccb (acaaac)^1020 (acaaa)^251 cc1"),
]
DELTAS = {"phase 3": {"u": 1, "p": 12, "q": 72, "r": -144}, "phase 4": {"u": 1, "p": 12, "q": -72, "r": 144}}


def cells(x):
    return "".join(E[ch] if ch in E else ("".join(E[y] for y in U) if ch == "U" else ch) for ch in x)


def parse(cs):
    out = []
    for part in cs.split():
        m = re.fullmatch(r"\((\w+)\)\^(\d+)", part)
        out += [(m.group(1), int(m.group(2)))] if m else [(ch, 1) for ch in part]
    return out


def symbolic(cs, var, offs):
    toks = ["L"]
    for wl, n in parse(cs):
        if wl in var:
            v = var[wl]
            toks.append(f"({cells(wl)})^{v}+{offs[v]}")
        else:
            toks.append(cells(wl) * n)
    return symtm.Config.parse(" ".join(toks) + " D> 0^inf")


def run_visits(m, c, k):
    for _ in range(k):
        n0 = c.steps
        c = symtm.run(m, c, lambda x: x.state == 3 and x.right == [symtm.Blank()] and not (x.steps - n0).is_zero(),
                      rotate=True, max_moves=10 ** 6)
        nf = tapeeq.normal(tapeeq.outward_left(c))[0]
        c.left = [symtm.Rep(tuple(reversed(t.word)), t.n) if isinstance(t, symtm.Rep) else t for t in reversed(nf)]
    return c


def main():
    m = symtm.Machine.parse(M)
    ok = True
    for name, P, var, cs in CYCLES:
        d = DELTAS[name]
        offs = {v: (1 if v == "u" else 3) + max(0, -d[v]) for v in var.values()}
        start = symbolic(cs, var, offs)
        fin = run_visits(m, start.copy(), P)
        target = symbolic(cs, var, {v: offs[v] + d[v] for v in offs})
        same = tapeeq.same(tapeeq.normal(tapeeq.outward_left(fin))[0], tapeeq.normal(tapeeq.outward_left(target))[0])
        ok &= same and fin.right == [symtm.Blank()] and fin.state == 3
        inc = ", ".join(f"{w} {d[v]:+d}" for w, v in var.items())
        print(f"{name}: {P} visits, {inc}: {'holds' if same else 'FAILS'} for all counts (offsets {offs}); "
              f"steps {fin.steps}")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
