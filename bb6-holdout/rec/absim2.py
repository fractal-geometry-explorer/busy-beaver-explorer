"""Event-driven abstract model. Marks: list of [type, pos] sorted; types G (gap, cells pos..pos+2), M (11 at pos, pos+1),
W (00 at pos, pos+1), B (111 at pos..pos+2). Content occupies 0..w-1. One active gap index or None."""
class Halt(Exception): pass

def round_step(w, marks, log=None):
    marks = [list(m) for m in marks]
    assert marks[0] == ['G', 1]
    active = 0
    def sort():
        nonlocal active
        a = marks[active] if active is not None else None
        marks.sort(key=lambda m: m[1])
        active = marks.index(a) if a is not None else None
    def ret(x):
        """packet travels left from x; returns 'round' if it reached the left end"""
        nonlocal active, w
        cands = [m for m in marks if m[1] < x and m[0] in ('G', 'W', 'B')]
        if not cands:
            return 'round'
        m = max(cands, key=lambda m: m[1])
        if m[0] == 'B': raise Halt("packet reaches block")
        if m[0] == 'G':
            m[1] += 2; active = marks.index(m); sort(); return None
        q = m[1]; marks.remove(m)
        marks.append(['M', q - 1]); g = ['G', q + 1]; marks.append(g); active = None; sort()
        active = marks.index(g); return None
    guard = 0
    while True:
        guard += 1
        if guard > 10000: raise RuntimeError("loop")
        g = marks[active]
        right = [m for m in marks if m[1] > g[1]]
        if not right:
            w += 3; marks.remove(g); active = None; marks.append(['M', w - 2]); sort()
            if log is not None: log.append(('end', g[1]))
            if ret(w - 2) == 'round': break
            continue
        m = min(right, key=lambda m: m[1])
        if m[0] == 'M':
            d = m[1] - g[1] - 3
            if d < 0: raise RuntimeError(f"neg d {d}")
            if d % 4 == 0:
                if log is not None: log.append(('swap', g[1], m[1]))
                m[1] = g[1] + d // 2 - 1; g[1] = g[1] + d // 2 + 1; sort(); continue
            if log is not None: log.append(('merge', g[1], m[1]))
            x = g[1] + d // 2 + 3
            marks.remove(g); marks.remove(m); active = None
            marks.append(['W', x]); sort()
            if ret(x) == 'round': break
            continue
        if m[0] in ('W', 'B'):
            if m[0] == 'W':
                if log is not None: log.append(('meet', g[1], m[1]))
                start = m[1]; marks.remove(g); marks.remove(m); active = None; keep_gap = None
            else:
                if log is not None: log.append(('block', g[1], m[1]))
                start = m[1] - 1; m[0] = 'W'; m[1] = start; keep_gap = g; active = None
            sort()
            nxt = [k for k in marks if k[1] > start]
            if not nxt:
                w += 2; marks.append(['M', w - 2]); sort()
                if ret(w - 2) == 'round': break
                continue
            k = min(nxt, key=lambda k: k[1])
            if k[0] == 'M':
                p2 = k[1]; marks.remove(k); ng = ['G', p2]; marks.append(ng); sort(); active = marks.index(ng); continue
            if k[0] == 'W':
                k[0] = 'B'
                if ret(k[1]) == 'round': break
                continue
            if k[0] == 'B':
                k[0] = 'W'; k[1] += 2; sort()
                if ret(k[1]) == 'round': break
                continue
            raise RuntimeError("shift into " + k[0])
        raise RuntimeError("gap meets " + m[0])
    # new round: left end
    extra = 2
    if marks and marks[0][0] == 'M' and marks[0][1] == 0:
        marks[0] = ['W', 1]; extra = 4
    w += extra
    out = [['G', 1]] + [[t, p + extra] for t, p in marks]
    return w, [tuple(m) for m in out]

def parse(line):
    parts = line.split()
    return int(parts[0]), int(parts[1][1:]), [(p[0], int(p[1:])) for p in parts[2:]]
def fmt(w, marks): return f"w{w} " + " ".join(f"{t}{p}" for t, p in marks)

if __name__ == "__main__":
    import sys
    lines = [l for l in open(sys.argv[1]) if l.strip()]
    ok = bad = err = 0
    for a, b in zip(lines, lines[1:]):
        s1, w1, m1 = parse(a); s2, w2, m2 = parse(b)
        try: pw, pm = round_step(w1, m1)
        except Exception as e:
            err += 1
            if err <= 10: print("ERR", s1, fmt(w1, m1), "->", fmt(w2, m2), e)
            continue
        if (pw, pm) == (w2, m2): ok += 1
        else:
            bad += 1
            if bad <= 10: print("MISMATCH", s1, fmt(w1, m1), "->", fmt(w2, m2), "pred", fmt(pw, pm))
    print("ok", ok, "bad", bad, "err", err)
