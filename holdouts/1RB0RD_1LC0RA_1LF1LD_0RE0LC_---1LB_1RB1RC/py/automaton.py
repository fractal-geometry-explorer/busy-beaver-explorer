"""The counter of 1RB0RD_1LC0RA_1LF1LD_0RE0LC_---1LB_1RB1RC as a 4-state automaton, checked against the machine.

usage: python3 automaton.py        (about a minute)

1. Runs the machine from blank tape and records the counter x0 x1 ... (the even cells right of the wall; every odd
   cell holds a 1) each time A arrives at x0 after crossing the wall.
2. `sweep(x)`: the machine run on the counter alone (a few pairs `10` of wall on its left, standing for the whole
   wall) until it leaves into the wall; checks that this reproduces every recorded sweep.
3. Finds the automaton: states are told apart by what `sweep` does to the next digits; prints its table.
4. Checks that the automaton gives `sweep` on random 80-digit counters, that `sweep` never halts and keeps the 1s on
   the odd cells for every counter of up to 16 digits (unless the carry runs off the end), and that it permutes the
   digit strings of each length k <= 12 (a causal permutation: cycles of power-of-two lengths).
5. End events: what the machine does when the carry runs past the last cell, in each of the three states, for both
   shapes of the right end (last cell a digit, as in the run from blank tape, or a separator, as after the first such
   event), with walls of 3 to 6 pairs.
"""
import itertools
import random

M = "1RB0RD_1LC0RA_1LF1LD_0RE0LC_---1LB_1RB1RC"


def table(m):
    t = {}
    for s, grp in enumerate(m.split("_")):
        for r in range(2):
            w = grp[3 * r:3 * r + 3]
            t[(s, r)] = None if w[0] == "-" else (int(w[0]), 1 if w[1] == "R" else -1, ord(w[2]) - 65)
    return t


T = table(M)


def blank_arrivals(steps):
    """[(step, wall pairs, counter digits x0..x110)] at each arrival of A at x0 (220 cells from the right end)."""
    n = 1 << 16
    tape = [0] * n
    pos = lo = hi = n // 2
    st, run, out = 0, 0, []
    for i in range(steps):
        w, d, q = T[(st, tape[pos])]
        tape[pos] = w
        pos += d
        st = q
        lo, hi = min(lo, pos), max(hi, pos)
        run = run + 1 if d == 1 else 0
        if st == 0 and tape[pos] == 1 and run >= 20 and hi - pos == 220:
            cells = tape[pos:hi + 1]
            assert all(cells[j] == 1 for j in range(1, len(cells), 2))
            assert tape[lo:pos] == [1, 0] * ((pos - lo) // 2)
            out.append((i + 1, (pos - lo) // 2, tuple(cells[0::2])))
    return out


def sweep(x, wall=4):
    """One sweep on the counter x (x[0] = 1): None if the carry leaves the cells given, else the new digits."""
    off = 2 * wall
    tape = [1, 0] * wall + [v for c in x for v in (c, 1)]
    pos, st = off, 0
    while True:
        t = T[(st, tape[pos])]
        if t is None:
            return "halt"
        tape[pos] = t[0]
        pos += t[1]
        st = t[2]
        if pos < off - 4:
            break
        if pos >= len(tape) - 1:
            return None
    if any(tape[off + 2 * i + 1] != 1 for i in range(len(x))):
        return "bad"
    return tuple(tape[off + 2 * i] for i in range(len(x)))


def pad(p, rng):
    while True:
        x = (1,) + p + tuple(rng.randint(0, 1) for _ in range(40))
        y = sweep(x)
        if isinstance(y, tuple):
            return x, y


def find_automaton(depth=6, rng=random.Random(5)):
    suf = list(itertools.product([0, 1], repeat=depth))

    def sig(p):
        return tuple(pad(p + s, rng)[1][1 + len(p):1 + len(p) + depth] for s in suf)
    reps, ids, trans = [()], {sig(()): 0}, {}
    i = 0
    while i < len(reps):
        p = reps[i]
        for a in (0, 1):
            pa = p + (a,)
            o = pad(pa, rng)[1][len(pa)]
            s = sig(pa)
            if s not in ids:
                ids[s] = len(reps)
                reps.append(pa)
            trans[(i, a)] = (o, ids[s])
        i += 1
        assert len(reps) < 50
    return trans


def apply(trans, x, start=0, ident=None):
    q, out = start, [x[0]]
    for d in x[1:]:
        o, q = trans[(q, d)]
        out.append(o)
    return tuple(out), q


def end_event(shape, k, wall, steps=100000):
    """The machine on wall + a counter of k ones, arranged so the carry runs to the end; 'digit' or 'sep' last."""
    if shape == "digit":
        cells, st, head = [1, 0] * wall + [1] + [1, 1] * k, 0, 2 * wall
    else:
        cells, st, head = [1, 0] * wall + [0, 0] + [1, 1] * k, 2, 2 * wall
    pad = 4000
    tape = [0] * pad + cells + [0] * 64
    pos, hi0 = head + pad, pad + len(cells) - 1
    hi = hi0
    for i in range(steps):
        t = T[(st, tape[pos])]
        if t is None:
            return f"halts at step {i}"
        tape[pos] = t[0]
        pos += t[1]
        st = t[2]
        hi = max(hi, pos)
        if pos < 2 or pos >= len(tape) - 2:
            return "leaves the window"
    return f"no halt in {steps} steps, {hi - hi0} new cells"


# the counter x0..x110 just before the sweep whose carry first runs past x110 (c/counter.c prints it)
BEFORE = ("1111111101011011010101011001101010101101110110101010110110110000000011111100111111110101100011111101110000"
          "11011")


def first_end_event(wall, steps=400000):
    """The machine on (10)^wall + the counter BEFORE: no halt, how many new cells on the right, and whether the
    sweeps after the event are again the automaton, now with the digits on the odd cells and the old wall turned into
    the counter's low digits.  Returns (halted, new cells, sweeps checked, sweeps that disagree)."""
    trans = AUTO
    cells = [1, 0] * wall + [v for i, c in enumerate(BEFORE) for v in ((int(c), 1) if i < len(BEFORE) - 1 else (int(c),))]
    pad = 4000
    tape = [0] * pad + cells + [0] * 64
    pos, st, hi0 = pad + 2 * wall, 0, pad + len(cells) - 1
    hi, run, rows = hi0, 0, []
    for i in range(steps):
        t = T[(st, tape[pos])]
        if t is None:
            return True, hi - hi0, 0, 0
        tape[pos] = t[0]
        if t[1] == 1:
            run += 1
        else:
            if run >= 30 and t[2] == 2 and hi > hi0:      # C turning after a long run right: one sweep's start
                rows.append(tuple(tape[pos:hi + 1]))
            run = 0
        pos += t[1]
        st = t[2]
        hi = max(hi, pos)
    ys = [r[1::2] for r in rows]
    bad = sum(1 for a, b in zip(ys, ys[1:]) if apply(trans, (1,) + a)[0][1:] != b)
    assert all(set(r[2::2]) == {1} for r in rows)
    return False, hi - hi0, len(ys) - 1, bad


AUTO = None


def main():
    global AUTO
    rec = blank_arrivals(3_000_000)
    print(f"{len(rec)} arrivals of A at x0 recorded, wall {rec[0][1]} to {rec[-1][1]} pairs")
    ok = sum(1 for (_, _, a), (_, _, b) in zip(rec, rec[1:]) if sweep(a) == b)
    print(f"sweep() reproduces {ok} of {len(rec) - 1} sweeps")
    assert ok == len(rec) - 1
    assert all(b[1] == a[1] + 1 for a, b in zip(rec, rec[1:]))
    trans = AUTO = find_automaton()
    names = "aebc"
    print("automaton (state: digit -> written digit, next state):")
    for q in range(len(trans) // 2):
        print("  " + names[q] + ": " + ", ".join(f"{d} -> {trans[(q, d)][0]} {names[trans[(q, d)][1]]}" for d in (0, 1)))
    rng = random.Random(9)
    for _ in range(3000):
        x = (1,) + tuple(rng.randint(0, 1) for _ in range(80))
        y = sweep(x)
        if isinstance(y, tuple):
            assert apply(trans, x)[0] == y
    print("the automaton agrees with sweep() on 3000 random 80-digit counters")
    seen = {}
    for k in range(1, 17):
        for bits in itertools.product([0, 1], repeat=k):
            y = sweep((1,) + bits)
            key = y if isinstance(y, str) else "runs off the end" if y is None else "ok"
            seen[key] = seen.get(key, 0) + 1
    print("sweep() on every counter of 1..16 digits:", seen)
    assert "halt" not in seen and "bad" not in seen
    for k in range(1, 13):
        img = {b: apply(trans, (1,) + b)[0][1:] for b in itertools.product([0, 1], repeat=k)}
        assert len(set(img.values())) == 2 ** k
        cyc, done = [], set()
        for b in img:
            c, n = b, 0
            while c not in done:
                done.add(c)
                c, n = img[c], n + 1
            if n:
                cyc.append(n)
        assert all(c & (c - 1) == 0 for c in cyc)
    print("on digit strings of each length k <= 12 the automaton is a permutation with cycles of length 2^j")
    print("end events (carry arriving at the right end in state a, b, c = k mod 3 with k ones):")
    for shape in ("digit", "sep"):
        for k in (30, 31, 32):
            res = {end_event(shape, k, w) for w in (3, 4, 5, 6)}
            print(f"  last cell a {shape}, state {'abc'[k % 3]}: " + "; ".join(sorted(res)))
    print("the first end event of the run from blank tape (carry in state c, last cell a digit), walls of n pairs:")
    for w in (1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 20, 33):
        halted, new, n, bad = first_end_event(w)
        assert not halted and new == 1 and bad == 0
        print(f"  n = {w}: no halt, 1 new cell, then {n} sweeps of the automaton on the n + 111 digits")


if __name__ == "__main__":
    main()
