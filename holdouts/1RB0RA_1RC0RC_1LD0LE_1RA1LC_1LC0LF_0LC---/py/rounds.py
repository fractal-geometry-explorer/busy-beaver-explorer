"""Round words: the tape at the moments the head is in state A on a new blank cell at the right end with a 0 on its
left (`0 u A>0`), decoded from the head outwards as V=1100, K=00, Q=10: the tokens of the Coq proof of the sibling
1RB0RA_1RC0LC_0LD1RF_1RA1LE_1LD0LB_0RE--- (busycoq PR 48), whose u_0 ... u_10 this reproduces.  Exact: the run is
the accelerated simulator clock.py (Hybrid), with a tick refused when it would extend the tape to the right, so
that every round boundary is reached cell by cell.  Lines with `?` are right-end visits that are not round words.

usage: python3 rounds.py MACHINE LOG10STEPS [SECONDS]      e.g. rounds.py 1RB0RA_1RC0RC_1LD0LE_1RA1LC_1LC0LF_0LC--- 80 60"""
import os, sys, time
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..",
                                "1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE", "py"))
import clock

def decode(cells):  # cells from the head outwards
    out = []; i = 0; n = len(cells)
    while i < n:
        a = cells[i]; b = cells[i+1] if i+1 < n else 0
        if a == 1 and b == 1:
            if i+3 < n+2 and (cells[i+2] if i+2<n else 0) == 0 and (cells[i+3] if i+3<n else 0) == 0:
                out.append("V"); i += 4
            else:
                out.append("?[%s]" % "".join(map(str, cells[i:]))); break
        elif a == 1: out.append("Q"); i += 2
        elif b == 0: out.append("K"); i += 2
        else:
            out.append("?[%s]" % "".join(map(str, cells[i:]))); break
    return "".join(out)

def rounds(m, limit, tmax=600):
    h = clock.Hybrid(m)
    last = h.hi; t0 = time.time()
    while h.t < limit and time.time() - t0 < tmax:
        if h.pos - 1 > h.lo:
            sv = (bytes(h.tp), h.pos, h.hi, h.lo, h.t, h.st, h.macros)
            if h.try_macro():
                if h.hi == sv[2]:
                    continue
                h.tp = bytearray(sv[0]); h.pos, h.hi, h.lo, h.t, h.st, h.macros = sv[1:]
        if not h.step():
            yield "HALT", h.t; return
        if h.pos > last and h.st == 0 and h.tp[h.pos] == 0:
            last = h.pos
            if h.tp[h.pos-1] == 0:
                cells = list(h.tp[h.lo:h.pos-1])[::-1]
                while cells and cells[-1] == 0: cells.pop()
                yield h.t, decode(cells)

if __name__ == "__main__":
    for t, u in rounds(sys.argv[1], 10 ** int(sys.argv[2]), float(sys.argv[3]) if len(sys.argv) > 3 else 600):
        print(clock.sci(t), len(u) if isinstance(u, str) else "", u, flush=True)
