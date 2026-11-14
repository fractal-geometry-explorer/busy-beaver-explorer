"""1RB1RA_1LC0LF_1RA1LD_1LB1LE_0LC0RD_---0RA as a map on words over two tokens of three cells, b = 110 and c = 111.

A *visit* is the head in B on the blank cell left of the tape.  At every visit the tape is a word over b and c
(c/wcheck.c: 74,198 visits in 2*10^10 steps), and the next visit shows F(w).  For w = b X, F(w) = b V(X) with

    (1) V(b X)           = c c X                 the visit ends at the first b it is handed
    (2) V(c c b c^n b Y) = c b c c b^n V(Y)      these two pass the visit on to the rest of the word
    (3) V(c b c^n b Y)   = c b b b^n V(Y)
    (4) V(c c c ...)     : not decoded (the long visits that rewrite the word deep inside or reach the right end)

usage: python3 words.py run STEPS     the visits of the run from blank tape against rules (1)-(3)
       python3 words.py all N         F on every word b X with |X| < N, blank tape on both sides: always a word again?
       python3 words.py F WORD        one visit
"""
import re, sys, itertools, collections

M = "1RB1RA_1LC0LF_1RA1LD_1LB1LE_0LC0RD_---0RA"
T = {}
for s in range(6):
    for b in range(2):
        t = M[s * 7 + b * 3:s * 7 + b * 3 + 3]
        if t[0] != '-':
            T[(s, b)] = (int(t[0]), 1 if t[1] == 'R' else -1, ord(t[2]) - 65)
TOK = {"b": (1, 1, 0), "c": (1, 1, 1)}
INV = {v: k for k, v in TOK.items()}


def word(cells):
    """cells (first cell = first cell of the tape) as a word, other tokens in brackets"""
    cells = list(cells)
    while cells and cells[-1] == 0:
        cells.pop()
    while len(cells) % 3:
        cells.append(0)
    return "".join(INV.get(tuple(cells[i:i + 3]), "[" + "".join(map(str, cells[i:i + 3])) + "]")
                   for i in range(0, len(cells), 3))


def F(w, limit=10 ** 7, pad=600):
    """the word at the next visit, from the visit on w (blank tape on both sides); 'HALT' if the machine halts"""
    cells = [0] * 60 + [x for t in w for x in TOK[t]] + [0] * pad
    p, s, lo = 59, 1, 60
    for n in range(limit):
        k = (s, cells[p])
        if k not in T:
            return "HALT"
        wr, d, s = T[k]
        cells[p] = wr
        p += d
        if p >= len(cells) - 1 or p < 0:
            return "PAD"
        if p < lo - 1 and n > 0:
            if s == 1:
                return word(cells[p + 1:])
            lo = p + 1
    return "LIMIT"


class Unknown(Exception):
    pass


def V(R):
    out = ""
    while True:
        if R.startswith("b"):
            return out + "cc" + R[1:]
        m = re.match(r'ccb(c*)b', R)
        if m:
            out += "cbcc" + "b" * len(m.group(1)); R = R[m.end():]; continue
        m = re.match(r'cb(c*)b', R)
        if m:
            out += "cbb" + "b" * len(m.group(1)); R = R[m.end():]; continue
        raise Unknown(R[:30])


def visits(steps):
    """the words at the visits of the run from blank tape"""
    N = 1 << 20
    tape = bytearray(N); p = N // 2; s = 0; lo = p; hi = p; out = []
    for step in range(steps):
        if p < lo and s == 1:
            out.append((step, word(tape[p + 1:hi + 1])))
        w, d, s = T[(s, tape[p])]
        tape[p] = w; p += d
        if p < lo - 1: lo = p + 1
        if p > hi: hi = p
    return out


def main(a):
    if a[0] == "run":
        vs = visits(int(float(a[1])))
        notword = sum(1 for _, w in vs if "[" in w)
        ok = unknown = wrong = 0
        heads = collections.Counter()
        for (_, w), (_, w2) in zip(vs[7:], vs[8:]):
            try:
                if not w.startswith("b"): raise Unknown(w)
                if "b" + V(w[1:]) == w2: ok += 1
                else: wrong += 1
            except Unknown as e:
                unknown += 1
                heads[len(re.match(r'c*', str(e)).group(0))] += 1
        print(f"{len(vs)} visits, {notword} of them not words over b, c; from visit 8 on: rules (1)-(3) give the next "
              f"word {ok} times, a wrong word {wrong} times, do not apply {unknown} times")
        print("  where they do not apply the rest starts with c^m, m:", dict(sorted(heads.items())))
    elif a[0] == "all":
        res = collections.Counter(); worst = (0, "")
        for n in range(int(a[1])):
            for t in itertools.product("bc", repeat=n):
                w = "b" + "".join(t)
                r = F(w)
                k = r if r in ("HALT", "PAD", "LIMIT") else ("other tokens" if "[" in r else "word")
                res[k] += 1
                if k == "word" and len(r) - len(w) > worst[0]: worst = (len(r) - len(w), w)
        print(dict(res), "largest growth:", worst)
    else:
        print(F(a[1]))


if __name__ == "__main__":
    main(sys.argv[1:])
