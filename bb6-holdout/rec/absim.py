"""Abstract round simulator for the closing-gap machine: state = (w, marks), gap at 1 at round start."""
def parse(line):
    parts = line.split()
    step, w = int(parts[0]), int(parts[1][1:])
    marks = [(p[0], int(p[1:])) for p in parts[2:]]
    return step, w, marks

def fmt(w, marks):
    return f"w{w} " + " ".join(f"{t}{p}" for t, p in marks)

def round_step(w, marks):
    """marks includes ('G',1) first. Returns next (w, marks) at the next round start, or raises."""
    assert marks[0] == ('G', 1), marks
    rest = list(marks[1:])
    left = []          # marks left behind (to the left of the active gap)
    g = 1
    grow_r = 0
    swapped_end = False
    i = 0
    while True:
        if i >= len(rest):
            # gap faces the blank end
            grow_r = 3 if swapped_end else None
            if grow_r is None: raise ValueError("gap meets blank end without swap: " + fmt(w, marks))
            new = left + [('M', w + grow_r - 2)]
            break
        t, p = rest[i]
        if t == 'M':
            d = p - g - 3
            if d < 0: raise ValueError(f"neg d {d} " + fmt(w, marks))
            if d % 4 == 0:
                left.append(('M', g + d // 2 - 1)); g = g + d // 2 + 1
                swapped_end = (i == len(rest) - 1 and p == w - 2)
                i += 1; continue
            else:
                new = left + [('W', g + d // 2 + 3)] + rest[i + 1:]
                grow_r = 0
                break
        elif t == 'W':
            # gap meets wall: shift to next mark
            if i + 1 >= len(rest):
                grow_r = 2; new = left + [('M', w + 2 - 2)]
                break
            t2, p2 = rest[i + 1]
            if t2 == 'M':
                g = p2; i += 2; swapped_end = False; continue
            if t2 == 'W':
                new = left + [('B', p2)] + rest[i + 2:]
                grow_r = 0
                break
            raise ValueError("shift into " + t2 + " " + fmt(w, marks))
        else:
            raise ValueError("unhandled mark " + t + " " + fmt(w, marks))
    w2 = w + 2 + grow_r
    return w2, [('G', 1)] + [(t, p + 2) for t, p in new]

if __name__ == "__main__":
    import sys
    lines = [l for l in open(sys.argv[1]) if l.strip()]
    ok = bad = err = 0
    for a, b in zip(lines, lines[1:]):
        s1, w1, m1 = parse(a); s2, w2, m2 = parse(b)
        try:
            pw, pm = round_step(w1, m1)
        except Exception as e:
            err += 1
            if err <= 12: print("ERR", s1, e)
            continue
        if (pw, pm) == (w2, m2): ok += 1
        else:
            bad += 1
            if bad <= 12: print("MISMATCH", s1, fmt(w1, m1), "->", fmt(w2, m2), "predicted", fmt(pw, pm))
    print("ok", ok, "bad", bad, "err", err)
