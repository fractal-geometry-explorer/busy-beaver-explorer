"""Mine event rules from the unmatched events of a run (shared by the batch-5 folders of G11).

usage: [MINER_FIRST=1] python3 miner.py M S WORDS PAIRS [MAX]   (MINER_FIRST=1: keep the copy of a run next to the head written out)
  M      the machine; S the event state
  WORDS  comma-separated digit words to generalize, longest first (e.g. 10101000110,1000110,0101,100)
  PAIRS  output of `c/evpair.c` (each unmatched event line followed by the next event line)
For each unmatched event (at most MAX distinct patterns), the window of cells the head visits until the next event
is cut out of the tape, runs of two or more copies of a word of WORDS are replaced by repeats with fresh variables,
and the rule from that pattern is proved by `autoev.event`.  Prints one line per new rule:
  RULE name|start|end|steps   and   COV <evcov rule line>
"""
import re
import sys
import os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from autoev import event, cov_line  # noqa: E402
from bbtools.machine import Machine as RefMachine  # noqa: E402,F401


def parse_m(m):
    t = {}
    for s, grp in enumerate(m.split("_")):
        for r in (0, 1):
            x = grp[3 * r:3 * r + 3]
            t[(s, r)] = None if x[2] == "-" else (int(x[0]), 1 if x[1] == "R" else -1, ord(x[2]) - 65)
    return t


def excursion(tm, tape, head, st, dt):
    tp = dict(enumerate(tape))
    pos, a, b = head, head, head
    for _ in range(dt):
        r = tp.get(pos, 0)
        w, d, s2 = tm[(st, r)]
        tp[pos] = w
        pos += d
        st = s2
        a, b = min(a, pos), max(b, pos)
    return a - head, b - head


FIRST_CONCRETE = os.environ.get("MINER_FIRST", "0") == "1"


def generalize(s, words, left):
    """replace runs (>=2) of words by (w)^v; for the left side, runs are taken next to the head first."""
    toks = []
    i = 0
    s2 = s[::-1] if left else s
    ws = [w[::-1] if left else w for w in words]
    while i < len(s2):
        best = None
        for w in ws:
            k = 0
            while s2.startswith(w, i + k * len(w)):
                k += 1
            if k >= 2 and (best is None or k * len(w) > best[1] * len(best[0])):
                best = (w, k)
        if best:
            if FIRST_CONCRETE:
                toks.append(("c", best[0]))
                toks.append(("rep", [best[0], best[1] - 1]))
            else:
                toks.append(("rep", [best[0], best[1]]))
            i += best[1] * len(best[0])
        else:
            toks.append(("c", s2[i]))
            i += 1
    if left:
        toks = [(k, [v[0][::-1], v[1]] if k == "rep" else v[::-1]) for k, v in toks[::-1]]
    return toks


runs = generalize


def main():
    m, S, words, pairs = sys.argv[1], sys.argv[2], sys.argv[3].split(","), sys.argv[4]
    mx = int(sys.argv[5]) if len(sys.argv) > 5 else 50
    tm = parse_m(m)
    seen = set()
    rawseen = set()
    lines = open(pairs).read().split("\n")
    prev = None
    nrule = 0
    for ln in lines:
        p = ln.split()
        if len(p) < 4:
            continue
        ev, t = int(p[0]), int(p[1])
        if prev and prev[0] + 1 == ev:
            L, R = prev[2].split("|")
            rk = L[-60:] + "|" + R[:60]
            if rk in rawseen:
                prev = (ev, t, p[3])
                continue
            rawseen.add(rk)
            tape = [int(c) for c in L + R]
            head = len(L)
            a, b = excursion(tm, tape, head, ord(S) - 65, t - prev[1])
            lw = L[max(0, len(L) + a - 1):] if a < 0 else ""
            atleft = len(L) + a - 1 < 0
            rw = (R + "0" * 70)[:max(b + 2, 1)]
            # strip trailing zeros beyond the tape into 0^inf
            atright = b + 2 > len(R)
            if atleft:
                lw = "0" * 3 + L
            gl = generalize(lw, words, True)
            gr = generalize(rw.rstrip("0") if atright else rw, words, False)
            # runs as (word, count); a run the symbolic run must split is written out
            def build(gl, gr):
                vs = iter("abcdefghijkmnpqrstuvwxyz")
                names = []
                def fmt(toks):
                    out = []
                    for k, v in toks:
                        if k == "rep":
                            nm = next(vs)
                            names.append((toks, v, nm))
                            out.append(f"({v[0]})^{nm}")
                        else:
                            out.append(v)
                    return " ".join(out)
                st = ("0^inf " if atleft else "L ") + fmt(gl) + f" {S}> " + fmt(gr) + (" 0^inf" if atright else " R")
                return st, names
            gl = runs(lw, words, True)
            gr = runs(rw.rstrip("0") if atright else rw, words, False)
            for _attempt in range(30):
                start, names = build(gl, gr)
                key = re.sub(r"\^[a-z]", "", start)
                if key in seen or nrule >= mx:
                    break
                try:
                    th, end, steps = event(m, f"r{nrule}", start, S)
                except Exception as e:  # noqa: BLE001
                    msg = str(e)
                    mm = re.search(r"NeedSplit \((\d+)\)\^(\w+)", msg) or re.search(r"\((\d+)\)\^(\w+)", msg)
                    hit = [x for x in names if mm and x[2] == mm.group(2)]
                    if not hit:
                        print(f"FAIL {start}: {type(e).__name__} {msg[:200]}", flush=True)
                        seen.add(key)
                        break
                    toks, v, nm = hit[0]
                    i = next(i for i, x in enumerate(toks) if x[0] == "rep" and x[1] is v)
                    toks[i:i + 1] = [("c", v[0] * v[1])]
                    continue
                seen.add(key)
                print(f"RULE r{nrule}|{start}|{end}|{steps}|ev {prev[0]} step {prev[1]}", flush=True)
                print("COV " + cov_line(f"r{nrule}", start), flush=True)
                nrule += 1
                break
        prev = (ev, t, p[3])


if __name__ == "__main__":
    main()
