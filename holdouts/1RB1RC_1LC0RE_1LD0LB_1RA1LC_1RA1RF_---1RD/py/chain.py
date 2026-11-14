"""1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA1RF_---1RD at the level of visits: the chain of mod-4 counters, exactly.

A *visit* is a step at which the head extends the tape to the left in state D.  The tape is then

    0^inf  D>0  1^n  R  0^inf ,        n even,

and one sweep later it is the same with n + 2 and a new R that does not depend on n (`visit`), unless the head
comes back in state C (an *event*: the block becomes a reservoir and n restarts at 2) or the machine halts.

Read in pairs a = 01, b = 11, the region R of an even visit is, for most of an epoch,

    a a a   S[s_0] S[s_1] ... S[s_{m-1}]   rest ,     S = [baabaa, abbabb, bbbbbb, aaaaaa]

a chain of m counters mod 4 (12 cells each) followed by older material.  One double visit adds 1 to s_0; if s_0 was
0 the sweep turns there, otherwise it goes on to s_1, and so on (`step_chain`).  So the number of double visits
that turn inside the chain before the first one that passes all of it is a closed formula in the states (`jump`),
with an exact step count (`jump_steps`); the double visit that passes the chain is simulated cell by cell
(`visit`, twice).  `run` alternates the two and is exact as long as its tests pass (`test_chain.py`):
every visit, R and step count of the direct run up to visit 60,000 (events at visits 97 and 1481 included).
"""
import sys

MACH = "1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA1RF_---1RD"


def parse(m):
    T = {}
    for i, row in enumerate(m.split("_")):
        for b in range(2):
            t = row[3 * b:3 * b + 3]
            T[(i, b)] = None if t[0] == "-" else (int(t[0]), 1 if t[1] == "R" else -1, ord(t[2]) - 65)
    return T


T = parse(MACH)
PAIR = {"a": (0, 1), "b": (1, 1)}


def cells(word):
    return bytes(x for ch in word for x in PAIR[ch])


S = [cells("baabaa"), cells("abbabb"), cells("bbbbbb"), cells("aaaaaa")]
SIDX = {S[i]: i for i in range(4)}
HEAD = cells("aaa")
SEAW = 16      # cells of the block kept in the simulated window (even); the rest is crossed by formula


def visit(n, R):
    """One sweep from  0^inf D>0 1^n R  (R: bytes of cells).

    Returns (kind, n', R', steps, depth): kind 'D' (the next visit; n' = n + 2), 'EVENT' (the head came back in state C;
    n' = 2 and R' = (fresh, tail): the new region is (01)^fresh followed by the cells `tail`), or 'HALT' (steps = the
    number of steps up to and including the halting one).  depth = how far into R the head went, in cells."""
    w = min(SEAW, n - n % 2)
    k = n - w                      # cells of the block left of the window: crossed in 2 steps a cell going right
    tape = bytearray(b"\x01" * w + bytes(R) + b"\x00" * 64)
    h, s, steps, mh = 0, 0, 1 + 2 * k, 0     # D0 -> 1RA, then A> 11 -> 01 A> (4 steps a pair)
    while h >= 0:
        if h >= len(tape):
            tape += b"\x00" * 64
        t = T[(s, tape[h])]
        if t is None:
            return ("HALT", n, None, steps + 1, mh - w)
        tape[h] = t[0]
        h += t[1]
        s = t[2]
        steps += 1
        if h > mh:
            mh = h
    if s == 3:                     # D< runs home over 1 (01)^(k/2): a step a cell, then D1 -> 1LC, C0 -> 1LD
        Rn = bytes(tape[w:]).rstrip(b"\x00")
        Rn += b"\x00" * (len(R) - len(Rn))
        return ("D", n + 2, Rn, steps + k + 2, mh - w)
    if s == 2:                     # C< turns 1 (01)^(k/2) into 0 (10)^(k/2), then C1 -> 0LB, B0 -> 1LC, C0 -> 1LD
        raw = bytes(tape).rstrip(b"\x00")            # so the tape is  D>0 1 1 | 0 (10)^(k/2) raw
        tail = b"\x00" + raw
        fresh = k // 2
        while tail[:2] == b"\x00\x01":
            tail = tail[2:]
            fresh += 1
        return ("EVENT", 2, (fresh, tail), steps + k + 3, mh - w)
    raise RuntimeError("the head left the window to the left in state " + "ABCDEF"[s])


def parse_chain(R):
    """The states of the chain at the start of R (None if R does not start with a a a)."""
    if R[:6] != HEAD:
        return None
    st, j = [], 6
    while j + 12 <= len(R):
        i = SIDX.get(bytes(R[j:j + 12]))
        if i is None:
            break
        st.append(i)
        j += 12
    return st


def set_chain(R, st):
    return R[:6] + b"".join(S[i] for i in st) + R[6 + 12 * len(st):]


def count(s, t, r):
    """Among t arrivals at a counter that starts in state s, how many find it in state r."""
    k0 = (r - s) % 4
    return 0 if t <= k0 else 1 + (t - 1 - k0) // 4


def arrivals(st, t0):
    """arr[j] = the number of sweeps that reach counter j during t0 double visits, none of which passes the chain."""
    arr, t = [0] * len(st), t0
    for j in range(len(st)):
        if t == 0:
            break
        arr[j] = t
        t -= count(st[j], t, 0)
    assert t == 0, "a sweep passes the chain"
    return arr


def jump(st):
    """(K, arr): K = the number of double visits that turn inside the chain before the first one that passes all
    of it, and the arrivals at each counter during them."""
    need, arr = 0, [0] * len(st)
    for j in range(len(st) - 1, -1, -1):
        k0 = (-st[j]) % 4                       # the first arrival that finds counter j at 0
        need += 0 if need < k0 else 1 + (need - k0) // 3
        arr[j] = need
    return need, arr


def jump_steps(st, arr, n):
    """The steps of arr[0] double visits that turn inside the chain, from block 1^n: a double visit costs 6n + 146
    steps, plus 128 for each counter it passes in state 1 or 3 and 108 for each it passes in state 2."""
    K = arr[0]
    tot = K * (6 * n + 146) + 12 * K * (K - 1)
    for j, t in enumerate(arr):
        if t == 0:
            break
        tot += 128 * (count(st[j], t, 1) + count(st[j], t, 3)) + 108 * count(st[j], t, 2)
    return tot


def run(v, n, R, steps=0, max_visit=None, max_pass=None, log=None, use_jump=True):
    """From the even visit v (block 1^n, region R) on.  Returns (kind, v, n, R, steps, ...) with kind 'LIMIT',
    'MAXPASS', 'EVENT' (v, n, R = the visit after the event, R as (fresh, tail); then the block before it) or
    'HALT' (steps = the halting step).  log(v, n, R, steps, what, data) is called after every jump and visit."""
    npass = 0
    while True:
        st = parse_chain(R) if use_jump else None
        if st:
            K, arr = jump(st)
            if max_visit is not None and v + 2 * K > max_visit:
                K = (max_visit - v) // 2
                arr = arrivals(st, K)
            if K > 0:
                steps += jump_steps(st, arr, n)
                R = set_chain(R, [(st[j] + arr[j]) % 4 for j in range(len(st))])
                v += 2 * K
                n += 4 * K
                if log:
                    log(v, n, R, steps, "jump", K)
        if max_visit is not None and v >= max_visit:
            return ("LIMIT", v, n, R, steps)
        depth = 0
        for _ in range(2):
            kind, n2, R2, s, d = visit(n, R)
            if kind == "HALT":
                return ("HALT", v, n, R, steps + s)
            steps += s
            v += 1
            if kind == "EVENT":
                if log:
                    log(v, n2, R2, steps, "EVENT", n)
                return ("EVENT", v, n2, R2, steps, n)
            n, R, depth = n2, R2, max(depth, d)
            if log:
                log(v, n, R, steps, "visit", d)
        npass += 1
        if log:
            log(v, n, R, steps, "pass", depth)
        if max_pass and npass >= max_pass:
            return ("MAXPASS", v, n, R, steps)


def direct(max_visit):
    """The direct run from blank tape: {visit: (step, n, R)} (steps counted as the number of transitions made)."""
    tape, h, s, lo, hi, v, out, k = {}, 0, 0, 0, 0, 0, {}, 0
    while v < max_visit:
        t = T[(s, tape.get(h, 0))]
        k += 1
        tape[h] = t[0]
        h += t[1]
        s = t[2]
        hi = max(hi, h)
        if h < lo:
            lo = h
            if s == 3:
                v += 1
                c = bytes(tape.get(i, 0) for i in range(lo + 1, hi + 1))
                n = len(c) - len(c.lstrip(b"\x01"))
                out[v] = (k, n, c[n:])
    return out


if __name__ == "__main__":
    # the state file of c/chainrun.c:  visit  block  steps  passes  R
    v, n, steps, passes, rs = open(sys.argv[1]).read().split()
    r = run(int(v), int(n), bytes(int(x) for x in rs), int(steps), max_pass=int(sys.argv[2]) if len(sys.argv) > 2 else 1)
    print(r[0], "visit", r[1], "block", r[2], "steps", r[4])
    if r[0] == "EVENT":
        print("fresh pairs", r[3][0], "tail cells", len(r[3][1]))
        print("tail", "".join(map(str, r[3][1])))
