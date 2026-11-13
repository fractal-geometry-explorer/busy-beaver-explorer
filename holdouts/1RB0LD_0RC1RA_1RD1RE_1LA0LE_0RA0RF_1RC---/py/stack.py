"""The stack run of 1RB0LD_0RC1RA_1RD1RE_1LA0LE_0RA0RF_1RC---.

  python3 py/stack.py run SEC     run the stack simulator for SEC seconds, one line per epoch
  python3 py/stack.py check N     compare the first N epochs with the plain C simulator (c/canon.c)

Between events the tape is  0^inf [1^n_k (01)^m_k 0] ... [1^n_2 (01)^m_2 0] 1^n_1 (01)^m_1 C> 0^inf,
held as the list stack = [(n_1, m_1), (n_2, m_2), ...].  Level-1 trips (lean/Rules.lean `trip`, `trips`) are done
in one go; a level 1 with n_1 = 1 is the same tape as level 2 with m_2 + m_1 + 1 (no steps).  Each event
(n_1 in {0, 2}) is computed by `rule` from the rules proved in lean/Rules.lean; when none applies, by direct
simulation with m_1 cut down to 30, 31 and 32 and extrapolated linearly in m_1 (the run reports how often).
Step counts are exact."""
import os, subprocess, sys, time
from collections import Counter
sys.set_int_max_str_digits(0)
HERE = os.path.dirname(os.path.abspath(__file__))
M = "1RB0LD_0RC1RA_1RD1RE_1LA0LE_0RA0RF_1RC---"


def parse(M):
    T = {}
    for i, g in enumerate(M.split('_')):
        for r in (0, 1):
            t = g[3 * r:3 * r + 3]
            T[('ABCDEF'[i], r)] = None if t[2] == '-' else (int(t[0]), 1 if t[1] == 'R' else -1, t[2])
    return T
T = parse(M)


def parse_stack(tape, h):
    i = h - 1; out = []
    while True:
        m = 0
        while i >= 1 and tape[i] == 1 and tape[i - 1] == 0: m += 1; i -= 2
        n = 0
        while i >= 0 and tape[i] == 1: n += 1; i -= 1
        out.append((n, m))
        if not any(tape[:i + 1]): return out
        i -= 1


def build(stack):
    s = ''
    for k, (n, m) in enumerate(reversed(stack)):
        s += '1' * n + '01' * m + ('0' if k < len(stack) - 1 else '')
    return s


def simulate(stack, cond, maxsteps=10**8):
    """Plain simulation from a stack configuration until cond(new stack) holds at a C-at-the-right-end configuration."""
    s = build(stack); pad = 6000
    tape = [0] * pad + [int(c) for c in s] + [0] * (pad * 30)
    h = pad + len(s); q = 'C'; hi1 = h - 1; st = 0
    while st < maxsteps:
        if q == 'C' and h > hi1 and st > 0 and tape[h - 1] == 1:
            S = parse_stack(tape, h)
            if cond(S): return st, S
        t = T[(q, tape[h])]
        if t is None: return st, 'HALT'
        tape[h] = t[0]
        if t[0] and h > hi1: hi1 = h
        elif not t[0] and h == hi1:
            while tape[hi1] == 0: hi1 -= 1
        h += t[1]; q = t[2]; st += 1
    return st, 'MAX'


def rule(n1, m1, rest):
    """(name, new stack, steps) by the rules of lean/Rules.lean, or None."""
    l2 = rest[0] if rest else None
    l3 = rest[1] if len(rest) > 1 else None
    if n1 == 0 and m1 >= 4:
        if l2 is None: return 'zero_blank', [(2 * m1 + 6, 3)], 4 * m1 + 45
        n2, m2 = l2
        if m2 >= 1: return 'zero_dec', [(2 * m1 + 7, 3), (n2, m2 - 1)] + rest[1:], None
        return 'zero_merge', [(n2 + 2 * m1 + 6, 3)] + rest[1:], None
    if n1 == 2 and m1 >= 12:
        if l2 is None: return 'two_blank', [(2 * m1 - 8, 3), (4, 6)], None
        n2, m2 = l2
        if n2 >= 3:
            if n2 == 4:   # level 2 becomes 1 (01)^(m2+7): the same tape as level 3 with m2 + 8 more copies of 01
                new = [(0, m2 + 8)] if l3 is None else [(l3[0], l3[1] + m2 + 8)] + rest[2:]
            else: new = [(n2 - 3, m2 + 7)] + rest[1:]
            return 'two_trip', [(2 * m1 - 4, 3)] + new, None
        if n2 == 0 and m2 >= 4:
            if l3 is None: return 'two_merge', [(2 * m1 - 8, 3), (2 * m2 + 4, 6)], None
            n3, m3 = l3
            if m3 >= 1: return 'two_dec', [(2 * m1 - 8, 3), (2 * m2 + 5, 6), (n3, m3 - 1)] + rest[2:], None
            return 'two_merge', [(2 * m1 - 8, 3), (n3 + 2 * m2 + 4, 6)] + rest[2:], None
    return None


M0 = 30
cache = {}
def event(n1, rest):
    """Event with level 1 = (n1, m), as (n'(m) = a + b m, m', steps(m) = sa + sb m, levels 2..), by simulation."""
    key = (n1, tuple(rest))
    if key in cache: return cache[key]
    outs = []
    for Mm in (M0, M0 + 1, M0 + 2):
        st, S = simulate([(n1, Mm)] + list(rest), cond=lambda S: S[0][0] >= 2 * M0 - 20)
        if not isinstance(S, list): raise RuntimeError(f"event {key} m1={Mm}: {S} after {st} steps")
        outs.append((st, S))
    (s0, S0), (s1, S1), (s2, S2) = outs
    assert S0[1:] == S1[1:] == S2[1:] and S0[0][1] == S1[0][1] == S2[0][1], (key, outs)
    dn, ds = S1[0][0] - S0[0][0], s1 - s0
    assert S2[0][0] - S1[0][0] == dn and s2 - s1 == ds, (key, outs)
    cache[key] = res = (S0[0][0] - dn * M0, dn, S0[0][1], s0 - ds * M0, ds, S0[1:])
    return res


def norm(stack):
    while len(stack) > 1 and stack[-1] == (0, 0): stack.pop()
    return stack


def run(maxsec=60, log=None, maxepochs=None):
    stack = [(0, 9)]; steps = 89          # lean/Rules.lean `start`
    kinds = Counter(); t0 = time.time(); ep = 0
    while time.time() - t0 < maxsec and (maxepochs is None or ep < maxepochs):
        n, m = stack[0]
        if n >= 3:
            k = n // 3 if n % 3 != 1 else (n - 1) // 3
            steps += k * (6 * (m - 1) + 30) + 15 * k * k      # `trips` with m - 1 for its m
            stack[0] = (n - 3 * k, m + 5 * k)
            continue
        if n == 1:
            stack = [(0, m + 1)] if len(stack) == 1 else [(stack[1][0], stack[1][1] + m + 1)] + stack[2:]
            continue
        a, b, mm, sa, sb, rest = event(n, stack[1:])   # step count (and the result, for the check below)
        new = norm([(a + b * m, mm)] + list(rest))
        r = rule(n, m, stack[1:])
        if r is None: kinds['simulated'] += 1
        else:
            assert norm(r[1]) == new, (n, m, stack, r, new)
            kinds[r[0]] += 1
        steps += sa + sb * m
        stack = new; ep += 1
        if log: log(ep, steps, stack)
    return ep, steps, stack, kinds


def short(x):
    return str(x) if x < 10**9 else f"~10^{len(str(x)) - 1}"


if __name__ == "__main__":
    if sys.argv[1] == "check":
        N = int(sys.argv[2]); ours = []
        run(maxepochs=N, log=lambda ep, st, S: ours.append((st, S[0])))
        exe = "/tmp/canon_47099"
        subprocess.run(["gcc", "-O2", "-o", exe, os.path.join(HERE, "..", "c", "canon.c")], check=True)
        lim = ours[-1][0] + 1
        out = subprocess.run([exe, str(lim)], capture_output=True, text=True).stdout.splitlines()
        theirs = [(int(l.split()[0]), (int(l.split()[2]), int(l.split()[4]))) for l in out if int(l.split()[2]) >= 3]
        print("epochs", len(ours), "agree" if theirs == ours else f"DIFFER\n{ours}\n{theirs}")
    else:
        sec = float(sys.argv[2]); last = [0]
        def log(ep, steps, S):
            print(ep, short(steps), [tuple(map(short, lv)) for lv in S], flush=True)
        ep, steps, stack, kinds = run(maxsec=sec, log=log)
        print("epochs", ep, "steps ~10^%d" % (len(str(steps)) - 1), dict(kinds))
