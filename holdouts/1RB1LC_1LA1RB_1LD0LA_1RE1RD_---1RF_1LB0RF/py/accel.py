"""Accelerated simulator for 1RB1LC_1LA1RB_1LD0LA_1RE1RD_---1RF_1LB0RF on the counter model.

Configurations (blank tape on both sides):

  X(k, W)    = C>0 1 0 1^(5k+3) 0 W
  Z(s, v, W) = (1 1 0^(5 a_1 - 2)) ... (1 1 0^(5 a_m - 2)) F>0 W

W = W_1 0 W_2 0 ... 0 W_r is a list of words separated by single 0s; each W_i = 1 x_0 1 x_1 ... 1 x_(b-1) is a
number N_i of b_i bits, least significant bit first.  (a_1, ..., a_m) is a composition of s, read as the (s-1)-bit
number v (a cut after position p sets bit s-1-p): v = 0 is (s), v = 2^(s-1)-1 is (1, ..., 1).  So the parts are a
binary counter, and every tick of it adds one to the first word.

Rules (each one-step rule is a kernel-checked theorem of lean/Rules.lean, written by rules.py):

  start  X(k, W) -> Z(k+2, 0, W)                                   5k + 22 steps        round_start
  tick   Z(s, v, N_1 ...) -> Z(s, v+1, N_1+1 ...)                    20 + 18 tau(v) + 4 tau(N_1)   tick_*
         (v < 2^(s-1)-1, N_1 < 2^b_1 - 1; tau = number of trailing 1 bits)
  end    Z(s, 2^(s-1)-1, N_1 ...) -> X(s-1, N_1+1 ...)               13(s-2) + 29 + 4 tau(N_1)     round_end*
  small  Z(s, v, 2^b-1 ...), v even, b >= 3: the first word becomes 2^(b+2) + 24 (b+3 bits), joined with the
         next word if there is one, and
           Z(s-1, v/2+1, ...)   in 103 + 4b + 18 tau(v/2) steps if v/2+1 < 2^(s-2)       small_*, small2_*
           X(s-2, ...)          in 99 + 4b + 13(s-2) steps otherwise                       small_last_*
  big    Z(s, v, 2^b-1 ...), v odd (or v = 2^(s-1)-1): not decoded; simulated directly with c/tmfrom until the
         next X configuration.

A round from X(k, N ...) without overflow therefore takes 84*2^k - 5 + 4(s2(N) - s2(N + 2^(k+1))) steps (s2 the
binary digit sum) and adds 2^(k+1) to N.

usage (from this folder; TMFROM=path of a compiled c/tmfrom, else it is compiled to /tmp):
  python3 accel.py regular            the closed form of a round against direct simulation (b <= 11)
  python3 accel.py rules SEED COUNT   jumps from random Z configurations (1 to 3 words) against a Python simulator
  python3 accel.py events FILE        every X configuration in a `tmfrom M A>0 STEPS C L K` listing of the run from
                                      blank tape, against the accelerated run from step 5,452
  python3 accel.py run EVENTS [MAXS]  the accelerated run from X(6, 215, 8) at step 5,452 (Lean: blank_X_5452),
                                      direct simulation of big restructures up to MAXS steps each
"""
import os, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import family  # noqa: E402

M = family.M


def tmf():
    exe = os.environ.get("TMFROM") or os.path.join(HERE, "..", "c", "tmfrom")
    if not os.path.exists(exe):
        exe = "/tmp/tmfrom_124655"
        if not os.path.exists(exe):
            subprocess.run(["gcc", "-O2", "-o", exe, os.path.join(HERE, "..", "c", "tmfrom.c")], check=True)
    family.TMF = exe
    return exe


def tau(x):
    t = 0
    while x & 1:
        x >>= 1
        t += 1
    return t


def s2(x):
    return bin(x).count("1")


def tau_sum(x, n):
    """sum of tau(x + i), i < n  (= number of carries when counting from x to x + n)."""
    return n - s2(x + n) + s2(x)


def v2c(s, v):
    C, cur = [], 1
    for p in range(1, s):
        if v >> (s - 1 - p) & 1:
            C.append(cur)
            cur = 1
        else:
            cur += 1
    return C + [cur]


def wcells(words):
    """W_1 0 W_2 0 ... : the pair-encoded words separated by single 0s."""
    cells = []
    for i, (N, b) in enumerate(words):
        if i:
            cells.append(0)
        for j in range(b):
            cells += [1, (N >> j) & 1]
    return cells


def parse_words(w):
    """Inverse of wcells (trailing blank ignored); None if the cells are not of that shape."""
    w = list(w)
    while w and w[-1] == 0:
        w.pop()
    words, N, b, i = [], 0, 0, 0
    while i < len(w):
        if w[i] == 1:
            N |= (w[i + 1] if i + 1 < len(w) else 0) << b
            b += 1
            i += 2
        else:
            if b == 0:
                return None
            words.append((N, b))
            N, b = 0, 0
            i += 1
    if b == 0:
        return None
    words.append((N, b))
    return tuple(words)


def ztape(s, v, words):
    cells = []
    for a in v2c(s, v):
        cells += [1, 1] + [0] * (5 * a - 2)
    h = len(cells)
    cells += [0] + wcells(words)
    return (family.rle(cells[:h]) + " F>" + family.rle(cells[h:])).strip()


def xtape(k, words):
    return "C>0 1 0 " + family.rle([1] * (5 * k + 3) + [0] + wcells(words))


def decode_x(cells):
    """('X', k, words) for C>0 1 0 1^(5k+3) 0 W with W a list of words, else None."""
    if not (len(cells) > 3 and cells[:3] == [0, 1, 0]):
        return None
    j = 3
    while j < len(cells) and cells[j] == 1:
        j += 1
    n = j - 3
    if n < 3 or (n - 3) % 5:
        return None
    ws = parse_words(cells[j + 1:])
    return ('X', (n - 3) // 5, ws) if ws else None


def regular_steps(k, N):
    return 84 * 2**k - 5 + 4 * (s2(N) - s2(N + 2**(k + 1)))


def direct(tp, maxs):
    """Run c/tmfrom from the tape to the next X configuration (any words): (steps, state) or (steps, None)."""
    exe = tmf()
    out = subprocess.run([exe, M, tp, str(maxs), "C", "L", "100000000"], capture_output=True,
                         text=True).stdout.splitlines()
    for l in out:
        if l.startswith('halted'):
            return int(l.split()[1]), ('HALT',)
        if l.startswith('running'):
            return int(l.split()[1]), None
        st, rest = l.split(None, 1)
        x = decode_x(family.cells(rest))
        if x:
            return int(st), x
    return maxs, None


def advance(state, T, log=None, maxs=10**9):
    """One rule application.  state: ('X', k, words) or ('Z', s, v, words); words = ((N1, b1), (N2, b2), ...),
    the counter acts on the first word.  Returns (state, T)."""
    if state[0] == 'X':
        _, k, ws = state
        (N, b), rest = ws[0], ws[1:]
        if N + 2**(k + 1) < 2**b:                      # a whole regular round at once
            return ('X', k + 1, ((N + 2**(k + 1), b),) + rest), T + regular_steps(k, N)
        return ('Z', k + 2, 0, ws), T + 5 * k + 22
    _, s, v, ws = state
    (N, b), rest = ws[0], ws[1:]
    top = 2**(s - 1) - 1
    if N < 2**b - 1 and v < top:
        n = min(top - v, 2**b - 1 - N)
        dt = 20 * n + 18 * tau_sum(v, n) + 4 * tau_sum(N, n)
        return ('Z', s, v + n, ((N + n, b),) + rest), T + dt
    if N < 2**b - 1 and tau(N) < b - 1:                # round_end needs a word cell after the carry
        return ('X', s - 1, ((N + 1, b),) + rest), T + 13 * (s - 2) + 29 + 4 * tau(N)
    if v % 2 == 0 and v < top and b >= 3:
        if log is not None:
            log.append(('small', T, s, v, ws))
        N2, b2 = 2**(b + 2) + 24, b + 3
        if rest:                                         # the next word is joined on
            N2, b2, rest = N2 + (rest[0][0] << b2), b2 + rest[0][1], rest[1:]
        if v // 2 + 1 < 2**(s - 2):
            return ('Z', s - 1, v // 2 + 1, ((N2, b2),) + rest), T + 103 + 4 * b + 18 * tau(v // 2)
        return ('X', s - 2, ((N2, b2),) + rest), T + 99 + 4 * b + 13 * (s - 2)
    if log is not None:
        log.append(('big' if v % 2 else 'end' if v == top else 'other', T, s, v, ws))
    d, x = direct(ztape(s, v, ws), maxs)
    return (x if x else ('UNKNOWN', ztape(s, v, ws))), T + d


def xevents(state, T, Tmax, maxs=10**9):
    """The X configurations from `state` on, until step Tmax: [(T, k, words)], and the restructure log."""
    out, log = [], []
    while T <= Tmax and state[0] in 'XZ':
        if state[0] == 'X':
            out.append((T, state[1], state[2]))
        state, T = advance(state, T, log, maxs)
    return out, log, state, T


def pyrun(cells, h, st, maxn):
    """A plain Python simulator, for the checks: the next Z or X configuration (any words)."""
    tr = {}
    for q, grp in enumerate(M.split('_')):
        for r in range(2):
            t = grp[3 * r:3 * r + 3]
            tr[(q, r)] = None if t[2] == '-' else (int(t[0]), 1 if t[1] == 'R' else -1, ord(t[2]) - 65)
    off = 4 * len(cells) + 1000
    t = bytearray(2 * off + 4 * len(cells))
    t[off:off + len(cells)] = bytes(cells)
    h += off
    lo, hi, n = off, off + len(cells), 0
    while n < maxn:
        r = tr[(st, t[h])]
        if r is None:
            return n + 1, ('HALT',)
        t[h], h, st, n = r[0], h + r[1], r[2], n + 1
        lo, hi = min(lo, h), max(hi, h)
        if (st == 5 or st == 2) and t[h] == 0:
            a = lo
            while a < h and t[a] == 0:
                a += 1
            if st == 2 and a == h:
                x = decode_x(list(t[h:hi + 2]))
                if x:
                    return n, x
            if st == 5 and t[h - 1] == 0 and a < h and t[h + 1] == 1:
                left, comp, i = list(t[a:h]), [], 0
                while i < len(left) and left[i:i + 2] == [1, 1]:
                    j = i + 2
                    while j < len(left) and left[j] == 0:
                        j += 1
                    g = j - i - 2
                    if (g + 2) % 5 or g < 3:
                        comp = None
                        break
                    comp.append((g + 2) // 5)
                    i = j
                ws = parse_words(t[h + 1:hi + 2])
                if comp and i == len(left) and ws:
                    s_, v_ = sum(comp), 0
                    pos = 0
                    for a_ in comp[:-1]:
                        pos += a_
                        v_ |= 1 << (s_ - 1 - pos)
                    return n, ('Z', s_, v_, ws)
    return n, None


def zcells(s, v, ws):
    cells = []
    for a in v2c(s, v):
        cells += [1, 1] + [0] * (5 * a - 2)
    return cells + [0] + wcells(ws), len(cells)


def main(a):
    tmf()
    if a[0] == 'regular':
        bad = tot = 0
        for b in range(2, 12):
            for k in range(0, b):
                for N in range(2**(b - 1), 2**b, max(1, 2**(b - 1) // 64)):
                    if N + 2**(k + 1) >= 2**b:
                        continue
                    r = family.chain(family.tape(k, N, b), 1, 200 * 2**k + 10**5)
                    tot += 1
                    if not r or r[0] != (regular_steps(k, N), family.regular(k, N, b)):
                        bad += 1
                        print("BAD regular", k, N, b, r, regular_steps(k, N))
        print("regular rounds: %d checked, %d wrong (steps and result)" % (tot, bad))
    elif a[0] == 'rules':
        # every Z rule (ticks in bulk, round end, small restructure) from random Z configurations with
        # 1 to 3 words, against the Python simulator: the next configuration and the step count
        import random
        random.seed(int(a[1]) if len(a) > 1 else 1)
        tot = bad = 0
        for _ in range(int(a[2]) if len(a) > 2 else 3000):
            s = random.randint(2, 9)
            v = random.randrange(2**(s - 1))
            ws = []
            for i in range(random.randint(1, 3)):
                b = random.randint(3 if i == 0 else 1, 8)
                N = random.randrange(2**(b - 1), 2**b)
                if i == 0 and random.random() < 0.5:
                    N = 2**b - 1 - random.randint(0, 2)
                ws.append((N, b))
            ws = tuple(ws)
            st = ('Z', s, v, ws)
            log = []
            pred, T = advance(st, 0, log, 10**6)
            if log and log[-1][0] != 'small':
                continue
            if pred[0] == 'Z' and pred[2] != v and not log:
                # a bulk jump: compare with that many single ticks
                pass
            cells, h = zcells(s, v, ws)
            t_, x = 0, None
            # run the Python simulator event by event until the predicted step count
            cur, hh, total = cells, h, 0
            got = None
            n, got = pyrun(cells, h, 5, T + 10)
            if got and got[0] == 'Z' and pred[0] == 'Z' and (n, got) != (T, pred):
                # the jump may skip intermediate ticks: follow the Z events
                n_acc, cfg = n, got
                while cfg and cfg[0] == 'Z' and n_acc < T:
                    c2, h2 = zcells(cfg[1], cfg[2], cfg[3])
                    m_, cfg = pyrun(c2, h2, 5, T + 10)
                    n_acc += m_
                n, got = n_acc, cfg
            tot += 1
            if (n, got) != (T, pred):
                bad += 1
                print("BAD", st, "predicted", T, pred, "got", n, got)
        print("Z rules: %d checked against direct simulation, %d wrong" % (tot, bad))
    elif a[0] == 'events':
        # every X event of a direct run (a `tmfrom ... C L` listing) against the accelerated run
        ev = []
        for l in open(a[1]):
            p = l.split(None, 1)
            if len(p) == 2 and p[1].startswith('C>0 1 0 '):
                x = decode_x(family.cells(p[1]))
                if x:
                    ev.append((int(p[0]), x[1], x[2]))
        first = [e for e in ev if e[0] >= 5452][0]
        acc, log, _, _ = xevents(('X', first[1], first[2]), first[0], ev[-1][0])
        dev = [e for e in ev if e[0] >= first[0]]
        print("direct X events from step %d to %d: %d; accelerated: %d; identical: %s" %
              (first[0], ev[-1][0], len(dev), len(acc), dev == acc))
        for l in log:
            print("  restructure %s at step %d, s=%d" % (l[0], l[1], l[2]))
    elif a[0] == 'run':
        import math
        state, T = ('X', 6, ((215, 8),)), 5452
        log = []
        for i in range(int(a[1])):
            if state[0] not in 'XZ':
                break
            state, T = advance(state, T, log, int(a[2]) if len(a) > 2 else 10**9)
        for l in log:
            print("%-6s at step %d (10^%.2f): s=%d, words (bits) %s" % (l[0], l[1], math.log10(l[1]), l[2],
                                                                         [b for _, b in l[4]]))
        if state[0] == 'X':
            print("now: step %d (10^%.2f) X(k=%d), words (bits) %s" % (T, math.log10(T), state[1],
                                                                       [b for _, b in state[2]]))
        else:
            print("now: step %d (10^%.2f) %s" % (T, math.log10(T), str(state)[:300]))


if __name__ == "__main__":
    main(sys.argv[1:])
