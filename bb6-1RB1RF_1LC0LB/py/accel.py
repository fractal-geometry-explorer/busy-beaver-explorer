"""Run the machine far past what any simulator reaches, with the counter steps done in closed form.

At a return of the head to the right end the tape is a token list (py/counter.py): irregular blocks at the left, then
levels. The levels on the right that satisfy the counter theorems (parities, and long enough) form a base-3 number V.
The next V trips are counter steps (lean/Counter.lean), so this program applies n <= V of them at once:

* level p (p = 0 the last one) is touched by the trips whose counter value u, before the trip, is a multiple of 3^p.
  Its digit then is (u / 3^p) mod 3: 2 or 1 means the trip turns there, 0 means it is passed and reset.
* digit 2 -> 1 and 0 -> 2 move one pair from W to g (the last level's W gains one instead); 1 -> 0 moves none (the
  last level's W gains two).
* the steps of one trip are a linear function of the lengths it touches, read off the pieces in lean/Rules.lean
  (`last2` 8a+8b+26, `turn2` 8a+8b+19, `walk0` 12c+4d+26, ...), summed here in closed form per level.

n is the largest count for which no level runs too short. The trips the theorems do not cover (the top of the
counter, py/counter.py) are run on the macro simulator (tools/py/bbtools/macro.py) from the token list, which keeps
blocks of any length run-length coded. Inside those, cycles the macro run repeats with counts changing linearly (a
wall drained a few pairs per round trip) are jumped over with rules that bbtools.cycles proves symbolically. Step counts are exact: tests/test_machine.py checks the program against the
plain macro run, return for return.

What rests on what: a bulk step is a sequence of instances of the counter theorems (kernel), but the bookkeeping that
applies them (this file) is trusted Python, as are the macro simulator and the cycle jumps (bbtools.cycles writes a
Lean theorem for each rule, but this program does not compile them) for the other trips.

usage: python3 accel.py STEPS [EVERY]     run to STEPS (1e30 is fine); print the state every EVERY trips run concretely
"""
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "tools", "py"))
from bbtools.macro import MacroRun  # noqa: E402
from bbtools import cycles  # noqa: E402
import counter  # noqa: E402

DIGIT = counter.DIGIT
SEPS = {2: ("1", "1"), 1: ("0", "1"), 0: ("0", "0")}
MIN_W = 6       # a level that is not the last one is used by the bulk step only while its W stays at least this


# ---------------------------------------------------------------- the levels
def regular(t):
    """The levels at the right end of token list t that satisfy the theorems, last level first:
    a list of [digit, g, W] and the index in t where the first of them (the leftmost) begins (its s_l)."""
    if len(t) < 5 or t[-2] != "0" or t[-1] != 1:
        return [], len(t)
    levs, i = [], len(t) - 5
    while i >= 1 and isinstance(t[i], int) and isinstance(t[i + 2], int):
        d = DIGIT.get((t[i - 1], t[i + 1]))
        if d is None:
            break
        g, w = t[i], t[i + 2]
        last = not levs
        par = 1 if d == 2 else 0
        if g % 2 != par or w % 2 != par or g < (1 if d == 2 else 2):
            break
        if last and w < (1 if d == 2 else 2):
            break
        if not last and w < MIN_W:
            break
        levs.append([d, g, w])
        i -= 4
    return levs, i + 3


def value(levs):
    v = 0
    for d, _, _ in reversed(levs):
        v = 3 * v + d
    return v


def _count(lo, hi, r):
    """#{k in [lo, hi] : k % 3 == r}"""
    if hi < lo:
        return 0
    return (hi - r) // 3 - (lo - 1 - r) // 3


def _touch_cost(d, last, g, w):
    if d == 2:
        return 4 * g + 4 * w + (18 if last else 3)
    if d == 1:
        return 4 * w + (16 if last else 1)
    return 8 * g + 4 * w + (23 if last else 8)


def bulk(levs, v, n):
    """Apply trips with counter values v, v-1, ..., v-n+1: (new levels, steps)."""
    out, steps = [], 0
    p3 = 1
    for p, (d, g, w) in enumerate(levs):
        last = p == 0
        lo, hi = -(-(v - n + 1) // p3), v // p3          # the k = u / 3^p of the trips touching level p
        # touches in time order: k = hi, hi-1, ..., lo; digit k % 3; m = moves so far (2s and 0s), l = 1s so far
        m = l = 0
        k = hi
        while k >= lo and k % 3 != 2:                     # the first partial cycle
            steps += _touch_cost(k % 3, last, g + m, w - m if not last else w + m + 2 * l)
            if k % 3 == 1:
                l += 1
            else:
                m += 1
            k -= 1
        cycles = (k - lo + 1) // 3 if k >= lo else 0
        if cycles:
            def cyc(i):
                mm, ll = m + 2 * i, l + i
                c = _touch_cost(2, last, g + mm, w - mm if not last else w + mm + 2 * ll)
                c += _touch_cost(1, last, g + mm + 1, w - mm - 1 if not last else w + mm + 1 + 2 * ll)
                c += _touch_cost(0, last, g + mm + 1, w - mm - 1 if not last else w + mm + 1 + 2 * ll + 2)
                return c
            f0, f1 = cyc(0), cyc(1)
            steps += cycles * f0 + (f1 - f0) * cycles * (cycles - 1) // 2
            m += 2 * cycles
            l += cycles
            k -= 3 * cycles
        while k >= lo:                                    # the last partial cycle
            steps += _touch_cost(k % 3, last, g + m, w - m if not last else w + m + 2 * l)
            if k % 3 == 1:
                l += 1
            else:
                m += 1
            k -= 1
        nd = ((v - n) // p3) % 3
        out.append([nd, g + m, w - m if not last else w + m + 2 * l])
        p3 *= 3
    return out, steps


def moves(levs, v, n):
    """Pairs each level loses from W over n trips (2s and 0s touched)."""
    res, p3 = [], 1
    for _ in levs:
        lo, hi = -(-(v - n + 1) // p3), v // p3
        res.append(_count(lo, hi, 2) + _count(lo, hi, 0))
        p3 *= 3
    return res


def max_trips(levs, v):
    """The largest n <= v for which every level but the last keeps W >= MIN_W."""
    def ok(n):
        mv = moves(levs, v, n)
        return all(levs[p][2] - mv[p] >= MIN_W for p in range(1, len(levs)))
    lo, hi = 0, v
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if ok(mid):
            lo = mid
        else:
            hi = mid - 1
    return lo


def with_levels(t, start, levs):
    t = list(t[:start])
    for d, g, w in reversed(levs):
        sl, sr = SEPS[d]
        t += [sl, g, sr, w]
    return t + ["0", 1]


# ---------------------------------------------------------------- the other trips, on the macro simulator
def macro_from_tokens(t):
    """A k=4 MacroRun at the return configuration of token list t: C reading the `0` of `0 10`, blank beyond."""
    r = MacroRun(counter.M, 4)
    r.state, r.dir = counter.C, 1
    r.right = [[(0, 0, 0, 0), 1], [(0, 1, 0, 0), 1]]
    left = []                       # blocks from the head leftwards
    cur = []                        # cells of the block being filled, right to left

    def emit(block, c=1):
        if left and left[-1][0] == block:
            left[-1][1] += c
        else:
            left.append([block, c])

    def cell(x):
        cur.append(x)
        if len(cur) == 4:
            emit(tuple(reversed(cur)))
            cur.clear()

    for tok in reversed(t[:-2]):    # the tail `0 1` is the right stack
        if isinstance(tok, str):
            cell(int(tok))
            continue
        cells = 2 * tok             # (10)^tok, read right to left: 0 1 0 1 ...
        i = 0                       # cells used; cell i is 0 if i is even
        while i < cells and cur:
            cell(i % 2)
            i += 1
        rest = cells - i
        if rest >= 4:
            # right to left the blocks read 0 1 0 1 (or 1 0 1 0 when a pair straddled the last block)
            emit((1, 0, 1, 0) if i % 2 == 0 else (0, 1, 0, 1), rest // 4)
            i += 4 * (rest // 4)
        while i < cells:
            cell(i % 2)
            i += 1
    if cur:
        while len(cur) < 4:
            cur.append(0)
        emit(tuple(reversed(cur)))
    r.left = [[(0, 0, 0, 0), 1]] + list(reversed(left))
    return r


def _at_return(r):
    return r.state == counter.C and r.dir == 1 and len(r.right) == 2 and r.right[1] == [(0, 1, 0, 0), 1]


def concrete_trip(t, accelerate=True):
    """Run from token list t on the macro simulator to the next return: (new token list, steps), or raise on a halt.
    With `accelerate`, cycles the macro run repeats (a wall drained one block per round trip) are jumped over with
    rules proved by bbtools.cycles; a jump may pass over whole returns, so one call can cover several trips."""
    r = macro_from_tokens(t)
    acc = None
    if accelerate:
        global ACC
        if ACC is None:
            ACC = cycles.Accelerator(r)
        acc = ACC
        acc.run_, acc.hist = r, {}      # the proved rules are kept from trip to trip
    while True:
        if not r.step():
            raise RuntimeError(f"HALT {r.steps} steps into a concrete trip from {t}")
        if _at_return(r):
            return counter.blocks(counter.items(r)), r.steps
        if acc is not None and acc.sample(r):
            snap = cycles.snapshot(r)
            h = acc.hist.pop(snap.key(), [])
            acc.hist[snap.key()] = h
            if len(acc.hist) > cycles.HIST_KEYS:
                del acc.hist[next(iter(acc.hist))]
            h.append(snap)
            del h[:-3]
            if acc.jump():
                JUMPS.append(acc.jumps[-1])
                if _at_return(r):
                    return counter.blocks(counter.items(r)), r.steps


ACC = None
JUMPS = []      # (steps before, cycles, steps after, rule name) of every cycle jump, steps counted within the trip


# ---------------------------------------------------------------- the driver
def run(steps, start=None, report=None):
    """From the return state `start` = (steps, tokens) (default: the first return of the blank run) until
    `steps`.  Yields (steps, trips, tokens, kind) after each bulk ('bulk') or concrete ('top' or 'proved') trip."""
    if start is None:
        start = next(iter(counter.returns(10 ** 6)))
    s, t = start
    trips = 0
    while s < steps:
        levs, i0 = regular(t)
        v = value(levs)
        n = max_trips(levs, v) if levs else 0
        if n > 0:
            nl, c = bulk(levs, v, n)
            t = with_levels(t, i0, nl)
            s += c
            trips += n
            yield s, trips, t, "bulk"
            continue
        p, _ = counter.predict(t)
        nt, c = concrete_trip(t)
        s += c
        trips += 1
        t = nt
        yield s, trips, t, "proved" if p is not None else "top"


def main(argv):
    if not argv:
        sys.exit(__doc__)
    steps = int(float(argv[0]))
    every = int(argv[1]) if len(argv) > 1 else 50
    k = 0
    for s, trips, t, kind in run(steps):
        if kind == "top":
            k += 1
            if k % every == 0:
                print(f"{float(s):.4e} steps  {float(trips):.4e} trips  {len(t)} tokens:", " ".join(map(str, t[:14])),
                      flush=True)
    print(f"reached {float(s):.4e} steps ({s}) after {trips} trips, {k} of them at the top; no halt")
    print(" ".join(map(str, t)))


if __name__ == "__main__":
    main(sys.argv[1:])
