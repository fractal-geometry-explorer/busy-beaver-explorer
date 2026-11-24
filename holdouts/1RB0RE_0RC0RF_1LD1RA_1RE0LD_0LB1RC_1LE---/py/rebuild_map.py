"""The rebuild map of 1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE---: from one single block to the next, as arithmetic.

A *rebuild state* is the moment a single block arrives: `enc (k + 1) [] l us` in Lean, a single block of 3(k + 1)
cells and a counter (l, us).  Through rebuild 400 of the run from blank tape (`check-run`) the counter is *regular*
there (l = 1 mod 4, every gap 3 mod 4), so it is a number: in round m with rem sub-rounds left (py/model.py `enc`/`dec`;
the bits of rem, lowest first, are 0^t 1^n1 0 1^(n2-1) 0 1^(n3-1) ... for l = 4t + 1 and gaps 4 n_i - 1).

The *transient* is everything from the rebuild sub-round to the first later moment at which the counter is regular
again (the small gaps).  What it does, found on the run and checked here:

  * it reads the lowest 3J bits of rem, for a J >= 1 that only those bits decide (a prefix code of 3-bit groups,
    `stops`, recognised by a 7-state automaton `AUTO`);
  * the list gains 4J - 1 units: the moment it ends is `enc 1 D l' us'` with mass 1 + sum(d + 1) = k + 4J, so the next
    single block has 3(k + 4J) cells;
  * the counter left is regular, in round m - 3J + 1 with rem' = 2 (Y - 1), Y = rem >> 3J;
  * the list left is T(D) = 2^(k + 4J - 1) - 1 - e(w): a deficit e that depends only on the word w of the 3J bits.

The collapse then takes T(D) sub-rounds (proved: `collapse_regular`), so the next rebuild state is pure arithmetic:

    k'   = k + 4J - 1
    V    = 2^(m - 3J + 2) - 2 (Y - 1)          (sub-rounds counted from the start of round 0, as `jump` does)
    V'   = V + 2^(k + 4J - 1) - 1 - e(w)
    m'   = floor(log2 V'),  rem' = 2^(m' + 1) - V'.

Here J and e(w) are computed from w alone by the pass machine (py/passm.py, the moves of lean/General.lean) on a
small configuration, the single block and the bits above w replaced by small ones; `check-local` tests that the result
does not depend on them, and `check-run` that the map gives the rebuild states of the run of py/gen_chain.py.

usage: python3 py/rebuild_map.py check-run R          rebuilds 4 .. R of py/gen_chain.py against the map (R <= 200: minutes)
       python3 py/rebuild_map.py check-local N        N random rebuild states: J, e and rem' do not depend on k or on the
                                                      bits above w, and rem' = 2 (Y - 1)
       python3 py/rebuild_map.py auto D               the stop/go tree of the code to depth D groups against AUTO
       python3 py/rebuild_map.py run R [SECONDS]      R rebuilds by the map from the third single block
"""
import os, random, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import model, passm  # noqa: E402
import gen_chain as gc  # noqa: E402
sys.set_int_max_str_digits(0)

# the automaton of the code: state -> next state for the group value 0..7 (bits lowest first: b0 + 2 b1 + 4 b2)
AUTO = {'A': 'ABCCD.AE', 'B': 'BFBB.C..', 'C': 'BCCD.AEC', 'D': '.BCCG.EE',
        'E': '..CCGGEE', 'F': 'F..CCGGE', 'G': 'FBB.C..G'}          # '.': the transient stops after this group


def auto_J(rem, maxJ=10 ** 6):
    """the J the automaton reads off the low bits of rem"""
    s = 'A'
    for j in range(1, maxJ):
        s = AUTO[s][(rem >> (3 * (j - 1))) & 7]
        if s == '.': return j
    return None


def lean_counter(m, rem):
    """(l, us) in Lean's coding (first gap without the head's cell) of the regular counter in round m, rem left"""
    l, segs = model.enc(m, rem)
    gaps = model.to_gaps(segs)
    return l, ([gaps[0] - 1] + gaps[1:]) if gaps else []


def num_counter(l, us):
    segs = ([us[0] + 1] + [u + 1 for u in us[1:]]) if us else []
    return model.dec(l, segs)


def reg(l, us):
    return l % 4 == 1 and all(u % 4 == 3 for u in us)


def transient(k, m, rem, maxseg=100000):
    """from the rebuild state (single block 3(k + 1), counter (m, rem)) to the first moment with a list and a regular
    counter: ("ok", D, m', rem', sub-rounds) or ("halt",) / ("stuck",) / ("collapsed",).  Passes by the pass machine,
    the stretches between them by `advance_to` (W and the counter, many sub-rounds at once), as py/gen_chain.py."""
    q, D = k + 1, []
    l, us = lean_counter(m, rem)
    S = 0
    for _ in range(maxseg):
        if D and reg(l, us):
            if q != 1: return ("q",)
            m2, r2 = num_counter(l, us)
            return "ok", D, m2, r2, S
        M = gc.gmax(gc.T(D), (l, us))[0] if D else 0
        if M > 0:
            y, _ = gc.gfast(M, (l, us))
            mm = q + gc.lmass(D); D2 = gc.Tinv(gc.T(D) - M); q = mm - gc.lmass(D2); D = D2; l, us = y; S += M
            if not D: return ("collapsed",)
            continue
        bs, ll, uu = [3 * d + 2 for d in D] + [3 * q], l, list(us)
        while True:
            r = passm.sub_fast(bs, ll, uu)
            if r[0] != "moment": return (r[0],)
            _, bs, ll, uu, n = r; S += 1
            e = gc.as_enc(bs)
            if e and e[1] and gc.gstep((ll, uu)) is not None: break
        (q, D), l, us = e, ll, list(uu)
    return ("maxseg",)


def word(k, m, rem):
    """(J, e, sub-rounds of the transient) of the rebuild state, from the transient itself"""
    r = transient(k, m, rem)
    if r[0] != "ok": return r
    _, D, m2, r2, S = r
    J = (m - m2 + 3) // 3
    if 3 * J + 4 > rem.bit_length(): return ("short",)       # the transient reached the top of the counter
    s = sum(d + 1 for d in D)
    assert s == k + 4 * J - 1 and m2 == m - 3 * J + 1 and r2 == 2 * ((rem >> (3 * J)) - 1), (k, m, rem)
    return J, (1 << s) - 1 - gc.T(D), S


_memo = {}


def local_word(rem, low=None):
    """(J, e, S) for the low bits of rem, on a small configuration: the lowest `low` bits of rem with one 1 above
    them, and a single block of 3(4 low / 3 + 25) cells; `low` starts a little above what the automaton reads
    and is doubled until the word fits"""
    if low is None:
        J0 = auto_J(rem, rem.bit_length() // 3 + 2)
        low = 3 * (J0 or 8) + 24
    while True:
        w = rem & ((1 << low) - 1)
        key = (w, low)
        if key not in _memo:
            m = low + 1; r = w | (1 << low)          # rem <= 2^m; the bits above `low` replaced by one 1
            _memo[key] = word(4 * low // 3 + 24, m, r)
        res = _memo[key]
        if res[0] in ("halt", "stuck") or (isinstance(res[0], int) and 3 * res[0] + 6 <= low): return res
        low *= 2


def step(k, m, rem):
    """the rebuild map: (k', m', rem', sub-rounds from this rebuild state to the next) or a failure"""
    res = local_word(rem)
    if not isinstance(res[0], int): return res
    J, e, S = res
    Y = rem >> (3 * J)
    if Y == 0: return ("short",)
    m1, r1 = m - 3 * J + 1, 2 * (Y - 1)
    V = (1 << (m1 + 1)) - r1
    Te = (1 << (k + 4 * J - 1)) - 1 - e
    V2 = V + Te
    m2 = V2.bit_length() - 1
    return k + 4 * J - 1, m2, (1 << (m2 + 1)) - V2, S + Te


def third():
    """the rebuild state of the third single block (rebuild 3 of the run; lean/Transient.lean, py/gen_chain.py)"""
    l, us = gc.gfast(536840942, (9, [3] * 7))[0]
    m, rem = num_counter(l, us)
    return 29, m, rem


def main():
    cmd = sys.argv[1]
    if cmd == "check-run":
        R = int(sys.argv[2]); t0 = time.time()
        k0, m0, r0 = third()
        segs = gc.segments(30, [], *lean_counter(m0, r0), R)
        print(f"py/gen_chain.py through rebuild {R}: {len(segs)} segments [{time.time() - t0:.0f} s]")
        states = [(k0, m0, r0)]; bad = irregular = 0
        for s in segs:
            if s["kind"] == "adv" and not s["D2"]:
                l, us = s["y"]
                if not reg(l, us): irregular += 1; continue
                m, rem = num_counter(l, us); states.append((s["q2"] - 1, m, rem))
        k, m, rem = states[0]
        for i, want in enumerate(states[1:]):
            got = step(k, m, rem)[:3]
            if got != want: bad += 1; print(f"rebuild {i + 4}: the map gives k = {got[0]}, the run k = {want[0]}")
            k, m, rem = want
        print(f"rebuilds 4 .. {len(states) + 2}: counter regular at all but {irregular}; the map gives the next rebuild "
              f"state exactly for {len(states) - 1 - bad} of {len(states) - 1} [{time.time() - t0:.0f} s]")
        sys.exit(1 if bad or irregular else 0)
    if cmd == "check-local":
        N = int(sys.argv[2]); random.seed(11); bad = 0; Js = {}
        for i in range(N):
            m = random.randint(30, 90); rem = random.randint(1, 1 << m)
            if rem < 1 << (m - 8): continue
            a = word(m + random.randint(0, 9), m, rem)
            if a == ("short",): continue
            if not isinstance(a[0], int): print("no word:", a, m, rem); bad += 1; continue
            J = a[0]
            if 3 * J + 6 > m: continue
            # the same low 3J + 3 bits, other bits above, another single block
            m2 = m + random.randint(0, 20)
            hi = random.randint(1, 1 << (m2 - 3 * J - 3)) - 1
            rem2 = (rem & ((1 << (3 * J + 3)) - 1)) | (hi << (3 * J + 3))
            if not 1 <= rem2 <= 1 << m2: continue
            b = word(m2 + random.randint(4 * J, 4 * J + 30), m2, rem2)
            # the parity of Y can matter only through rem' = 2 (Y - 1), which `word` asserts
            if a[:2] != b[:2] or auto_J(rem) != J: bad += 1; print("DIFFERENT", m, rem, a[:2], b[:2], auto_J(rem))
            Js[J] = Js.get(J, 0) + 1
        print(f"{N} random rebuild states: J, e from the low bits alone, rem' = 2 (Y - 1) and the automaton's J; "
              f"{bad} failures; J seen: {dict(sorted(Js.items()))}")
        sys.exit(1 if bad else 0)
    if cmd == "auto":
        Dp = int(sys.argv[2]); random.seed(2); bad = n = 0
        frontier = [""]
        for d in range(Dp):
            nf = []
            for p in frontier:
                for v in range(8):
                    w = p + format(v, '03b')[::-1]
                    low = len(w)
                    for _ in range(2):
                        m = low + 40
                        tail = "".join(random.choice("01") for _ in range(m - low))
                        rem = int((w + tail)[::-1], 2)
                        J = word(4 * m, m, rem)[0]; n += 1
                        if auto_J(rem) != J: bad += 1; print("AUTO DIFFERS", w, J, auto_J(rem))
                    if J > d + 1: nf.append(w)
            frontier = nf
        print(f"stop/go tree to depth {Dp}: {n} rebuild states, the automaton differs on {bad}")
        sys.exit(1 if bad else 0)
    if cmd == "run":
        R = int(sys.argv[2]); tmax = float(sys.argv[3]) if len(sys.argv) > 3 else 1e18
        k, m, rem = third(); t0 = time.time(); subs = 0; Jmax = 0
        for i in range(4, R + 1):
            r = step(k, m, rem)
            if not isinstance(r[0], int): print(f"rebuild {i}: {r}"); sys.exit(1)
            Jmax = max(Jmax, (r[0] - k + 1) // 4)
            k, m, rem, S = r; subs += S
            if i % 100 == 0 or i == R:
                print(f"rebuild {i}: single block {3 * (k + 1)} cells, round {m}, more than 2^{subs.bit_length() - 1} "
                      f"sub-rounds; longest word so far {Jmax} groups [{time.time() - t0:.0f} s]", flush=True)
            if time.time() - t0 > tmax: break


if __name__ == "__main__":
    main()
