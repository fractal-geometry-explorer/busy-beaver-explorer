"""The A-event map of 1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_---1RA, checked against direct simulation and iterated.

Sample the run when the head is in state A at the left end of the tape.  From step 118 on the tape is then one of

    U(a, b) = A> 011011 1^a 0 1^b        V(a, b) = A> 1110 1^a 0 1^b

(blank elsewhere), or the configuration 3 steps after a V-event (not used).  Writing s for the same letter as the
start and o for the other one, the next U/V-event is (for a >= 15; for odd a < 15 see
`step`, and when also b < 30 the next event is found by direct simulation):

  a odd, b odd:   a = 1 mod 4  ->  o((3a-3)/2, b+8)  [from U]   o((3a-7)/2, b+8)  [from V]
                  a = 3 mod 4  ->  s((3a+3)/2, b+3)
  a odd, b even:  b >= a-7     ->  s(3a-5, b-a+8)
                  b <= a-13    ->  o(3b+26, a-b-12)  [U]   o(3b+24, a-b-12)  [V]       (b = 0: o(6, a-3))
                  b = a-11, a-9: U -> V(4, 3a-5), V(2, 3a);   V -> V(2, 3a-4), V(4, 3a-3)
  a even, b odd:  a = 2 mod 4  ->  o((3a+10)/2, b)
                  a = 0 mod 4  ->  s((3a+16)/2, b-5)  [U]   s((3a+20)/2, b-5)  [V]      if b >= 7
                                   b = 1: HALT;  b = 3: V(4, (3a+16)/2) [U], V(2, (3a+22)/2) [V];
                                   b = 5: V(4, (3a+14)/2) [U], U(4, (3a+18)/2) [V]
  a even, b even: b >= a+4     ->  s(3a+6, b-a-3)  [U]   s(3a+8, b-a-3)  [V]
                  b <= a-2     ->  o(3b+4, a-b-1)
                  b = a, a+2:  U -> V(4, 3a+6), V(2, 3a+11);   V -> V(2, 3a+9), V(4, 3a+10)

The machine halts exactly at U(a, 1) or V(a, 1) with a = 0 mod 4 (it reads the 1 in state F).

usage: python3 emap.py grid AMAX BMAX      direct simulation from every U/V(a, b), a < AMAX, b < BMAX, against the map
       python3 emap.py random N SEED       N random starts with 15 <= a, b < 2000
       python3 emap.py blank STEPS         the U/V-events of the run from blank tape, each checked against the map
       python3 emap.py far N               N map steps from the first U-event, U(4, 3) at step 118
       python3 emap.py mc S N              halting frequency of N random starts of size S (200 map steps each)
"""
import os, random, re, sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..",
                                "1RB0LA_0RC0RB_1LD1LA_1LC1RE_1RF0RD_1LC---", "py"))
import g01tools as g  # noqa: E402

M = "1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_---1RA"
PATS = [("U", re.compile(r"A011011(1*)0(1*)")), ("V", re.compile(r"A1110(1*)0(1*)"))]
START = {"U": "A> 011011 1^%d 0 1^%d", "V": "A> 1110 1^%d 0 1^%d"}
FIRST = (118, "U", 4, 3)
AMIN = 15


def step(t, a, b):
    """the next event (t', a', b'), 'HALT', or None when a < AMIN is odd and b < 30 (not covered)"""
    U = t == "U"
    s, o = t, ("V" if U else "U")
    if a % 2 == 0 and b % 2 == 1:
        if a % 4 == 2:
            return (o, (3 * a + 10) // 2, b)
        if b == 1:
            return "HALT"
        if b == 3:
            return ("V", 4, (3 * a + 16) // 2) if U else ("V", 2, (3 * a + 22) // 2)
        if b == 5:
            return ("V", 4, (3 * a + 14) // 2) if U else ("U", 4, (3 * a + 18) // 2)
        return (s, (3 * a + (16 if U else 20)) // 2, b - 5)
    if a % 2 == 0:
        if b >= a + 4:
            return (s, 3 * a + (6 if U else 8), b - a - 3)
        if b <= a - 2:
            return (o, 3 * b + 4, a - b - 1)
        if b == a:
            return ("V", 4, 3 * a + 6) if U else ("V", 2, 3 * a + 9)
        return ("V", 2, 3 * a + 11) if U else ("V", 4, 3 * a + 10)
    if a < AMIN:
        if b < 30:
            return None
        if a == 1:
            if U:
                return ("V", 2, b + 7) if b % 2 == 0 else ("V", 4, b + 5)
            return ("V", 4, b + 6) if b % 2 == 0 else ("V", 2, b + 8)
        if a % 4 == 1 and b % 2 == 1:
            return (s, (3 * a - 7) // 2, b + 7)
    if b % 2 == 1:
        if a % 4 == 1:
            return (o, (3 * a - (3 if U else 7)) // 2, b + 8)
        return (s, (3 * a + 3) // 2, b + 3)
    if b >= a - 7:
        return (s, 3 * a - 5, b - a + 8)
    if b == 0:
        return (o, 6, a - 3)
    if b <= a - 13:
        return (o, 3 * b + (26 if U else 24), a - b - 12)
    if b == a - 11:
        return ("V", 4, 3 * a - 5) if U else ("V", 2, 3 * a - 4)
    return ("V", 2, 3 * a) if U else ("V", 4, 3 * a - 3)


def direct(t, a, b, N=10**9):
    """the next U/V-event after t(a, b) by direct simulation: (t', a', b'), 'HALT', or None"""
    for k, tape in g.events(M, START[t] % (a, b), N, "A", "L"):
        if isinstance(tape, int):
            return "HALT" if k == "halted" else None
        if k == 0:
            continue
        for nm, p in PATS:
            mm = p.fullmatch(tape)
            if mm:
                return nm, len(mm.group(1)), len(mm.group(2))


def nxt(t, a, b):
    r = step(t, a, b)
    return direct(t, a, b) if r is None else r


def blank_events(N):
    for k, tape in g.events(M, "A> 0", N, "A", "L"):
        if isinstance(tape, int):
            return
        for nm, p in PATS:
            mm = p.fullmatch(tape)
            if mm:
                yield k, nm, len(mm.group(1)), len(mm.group(2))


def check(starts):
    bad = n = 0
    for t, a, b in starts:
        p = step(t, a, b)
        if p is None:
            continue
        n += 1
        d = direct(t, a, b)
        if d != p:
            bad += 1
            print("MISMATCH", t, a, b, "map", p, "direct", d, flush=True)
    return n, bad


if __name__ == "__main__":
    cmd = sys.argv[1]
    if cmd == "grid":
        A, B = int(sys.argv[2]), int(sys.argv[3])
        n, bad = check((t, a, b) for t in "UV" for a in range(A) for b in range(B))
        print(f"grid: {n} starts covered by the map, {bad} mismatches")
    elif cmd == "random":
        rnd = random.Random(int(sys.argv[3]))
        sts = []
        for i in range(int(sys.argv[2])):
            a = rnd.randrange(AMIN, 2000)
            b = rnd.choice([rnd.randrange(0, 40), rnd.randrange(0, 2 * a + 40), a + rnd.randrange(-14, 6)])
            sts.append((rnd.choice("UV"), a, b))
        n, bad = check(sts)
        print(f"random: {n} starts, {bad} mismatches")
    elif cmd == "blank":
        prev, n = None, 0
        for k, t, a, b in blank_events(int(float(sys.argv[2]))):
            if prev:
                p = nxt(*prev[1:])
                assert p == (t, a, b), (prev, (k, t, a, b), p)
                n += 1
            prev = (k, t, a, b)
            print(k, t, a, b, flush=True)
        print(f"blank: {n} events follow the map from the one before them")
    elif cmd == "mc":
        S, N = int(sys.argv[2]), int(sys.argv[3])
        rnd = random.Random(5)
        halts = unc = 0
        for i in range(N):
            t, a, b = rnd.choice("UV"), rnd.randrange(S, 2 * S), rnd.randrange(0, 2 * S)
            for j in range(200):
                r = step(t, a, b)
                if r in ("HALT", None):
                    halts += r == "HALT"
                    unc += r is None
                    break
                t, a, b = r
        print(f"mc: size {S}: {halts} of {N} starts halt within 200 map steps ({halts / N:.2e}); "
              f"{unc} reached an uncovered case")
    elif cmd == "far":
        k, t, a, b = FIRST
        stats = {"swap": 0, "small": 0}
        minb = b
        for i in range(int(sys.argv[2])):
            r = nxt(t, a, b)
            if r == "HALT":
                print("HALT after", i, "map steps")
                break
            if r is None:
                print("not covered:", t, a, b)
                break
            t2, a2, b2 = r
            if a2 < AMIN:
                stats["small"] += 1
            if a2 < a:
                stats["swap"] += 1
            t, a, b = t2, a2, b2
            minb = min(minb, b)
        print(f"far: {i + 1} map steps from U(4, 3) (step 118): no halt; now {t}(a, b) with a of {int(a.bit_length() * 0.30103) + 1} digits "
              f"and b of {int(b.bit_length() * 0.30103) + 1} digits; {stats['swap']} steps decreased a, {stats['small']} had a < {AMIN}; "
              f"smallest b {minb}")
