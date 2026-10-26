"""Round-by-round trace of one cycle (clean n -> next clean) in the mark model, with events."""
import sys

HOOK = None
CURRENT_EV = None

def round_events(w, marks):
    marks = sorted(([t, p] for t, p in marks), key=lambda m: m[1]); ev = []
    global CURRENT_EV
    CURRENT_EV = ev
    def hook(label, x=None):
        if HOOK: HOOK(marks, label, x)
    gap = marks[0]
    def first_right(x):
        r = [m for m in marks if m[1] > x]; return min(r, key=lambda m: m[1]) if r else None
    def shift_from(x):
        nonlocal w
        hook("shift", x)
        k = first_right(x)
        if k is None:
            w += 2; marks.append(["M", w - 2]); ev.append(f"shift→end(M{w-2})"); return packet_back(w - 2)
        if k[0] == "M": ev.append(f"shift→M{k[1]}=G"); k[0] = "G"; return k
        if k[0] == "W": ev.append(f"shift→W{k[1]}=B"); k[0] = "B"; return packet_back(k[1])
        if k[0] == "B": ev.append(f"shift→B{k[1]}=W{k[1]+2}"); k[0] = "W"; k[1] += 2; return packet_back(k[1])
    def packet_back(x):
        hook("packet", x)
        left = [m for m in marks if m[1] < x and m[0] != "M"]
        if not left: return None
        m = max(left, key=lambda m: m[1])
        if m[0] == "B": ev.append("HALT"); raise RuntimeError("halt")
        if m[0] == "G": ev.append(f"wake G{m[1]}→{m[1]+2}"); m[1] += 2; return m
        q = m[1]; m[0], m[1] = "M", q - 1; g = ["G", q + 1]; marks.append(g); ev.append(f"W{q}→M{q-1}+G{q+1}"); return g
    while gap is not None:
        hook("gap", gap[1])
        g = gap[1]; m = first_right(g)
        if m is None:
            marks.remove(gap); w += 3; marks.append(["M", w - 2]); ev.append(f"G{g}→end(M{w-2})"); gap = packet_back(w - 2)
        elif m[0] == "M":
            d = m[1] - g - 3
            if d % 4 == 0:
                ev.append(f"swap G{g}/M{m[1]} d={d}"); m[1] = g + d // 2 - 1; gap[1] = g + d // 2 + 1
            else:
                ev.append(f"merge G{g}/M{m[1]} d={d}→W{g+d//2+3}"); marks.remove(gap); m[0], m[1] = "W", g + d // 2 + 3; gap = packet_back(m[1])
        elif m[0] == "W":
            ev.append(f"G{g} meets W{m[1]}"); x = m[1]; marks.remove(gap); marks.remove(m); gap = shift_from(x)
        elif m[0] == "B":
            ev.append(f"G{g} passes B{m[1]}"); m[0], m[1] = "W", m[1] - 1; gap = shift_from(m[1])
        marks.sort(key=lambda k: k[1])
    extra = 2
    if marks and marks[0] == ["M", 0]: marks[0] = ["W", 1]; extra = 4; ev.append("M0→W")
    return w + extra, [["G", 1]] + [[t, p + extra] for t, p in marks], ev

def cycle(n, show=True):
    w = 2 * n + 6; marks = [["G", 1], ["M", w - 2]]; out = []
    for r in range(1, 10000):
        start = (w, [f"{t}{p}" for t, p in marks])
        w, marks, ev = round_events(w, marks)
        out.append((start, ev))
        if len(marks) == 2 and marks[1] == ["M", w - 2]:
            return (w - 6) // 2, out
    raise RuntimeError

if __name__ == "__main__":
    for n in map(int, sys.argv[1:]):
        m, out = cycle(n)
        print(f"n = {n} = {bin(n)}  ->  {m}  ({len(out)} rounds)")
        for (w, mk), ev in out:
            print(f"   w={w:<6} {' '.join(mk):40s} | {'; '.join(ev)}")
