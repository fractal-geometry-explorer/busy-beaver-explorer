"""Can the run of the rebuild map outgrow its counter or its list?  (py/rebuild_map.py, py/sym_law.py)

The law for every word (py/sym_law.py) holds as long as the transient ends below the top of the counter (the word,
3J bits, fits in the m bits of r with a few to spare) and the list is long enough for it (k >= 3z + 14, z the
number of leading zero groups of the word).  This script measures both along the run of the map and checks the
arithmetic that says where long words come from.

The map, with Y = r >> 3J, V = 2^(m-3J+2) - 2(Y-1) and the deficit e = e(w):

  * if V > e + 1 (*normal*):  m' = k',      r' = (2^k' - 2^(m-3J+2)) + (2Y - 1 + e),  0 <= 2Y - 1 + e < 2^(m-3J+2)
  * if V <= e + 1 (*drop*):   m' = k' - 1,  r' = 1 + e - V

so m is k or k - 1 at every rebuild, a normal rebuild puts a run of 1s of length k' - m + 3J - 2 on top of the bits
it did not read (shifted up by one), and a drop leaves r' far below 2^m': a stretch of 0s from the top of 1 + e - V
to the top of the counter.  Such a stretch is later read in states A, B or F of the automaton, which loop on the
zero group, three bits per group: the long words.

usage: python3 py/margins.py run R        rebuilds 4 .. R: the identities above at every rebuild, the largest 3J/m,
                                          the drops and the long words (R = 2000: 7 minutes, one word of 25,312
                                          groups takes most of it)
       python3 py/margins.py list N       N random words: the shortest list length k from which on the transient
                                          gives the word's J and e, against 3z
"""
import os, sys, random, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rebuild_map as rm  # noqa: E402


def zero_stretches(r, m, minl):
    """(position from the bottom, length) of the runs of at least minl 0 bits among the m bits of r"""
    s = bin(r)[2:].zfill(m)[::-1]; out = []; i = 0
    while i < len(s):
        j = s.find('1' if s[i] == '0' else '0', i)
        if j < 0: j = len(s)
        if s[i] == '0' and j - i >= minl: out.append((i, j - i))
        i = j
    return out


def run(R):
    t0 = time.time(); k, m, r = rm.third(); worst = (0, 0); drops = []; longw = []; bad = 0
    for i in range(4, R + 1):
        J, e, _ = rm.local_word(r)
        Y = r >> (3 * J); V = (1 << (m - 3 * J + 2)) - 2 * (Y - 1)
        k2, m2, r2, _ = rm.step(k, m, r)
        if 3 * J / m > worst[0]: worst = (3 * J / m, i)
        if V > e + 1:
            low = 2 * Y - 1 + e
            ok = (m2 == k2 and 0 <= low < 1 << (m - 3 * J + 2)
                  and r2 == (1 << k2) - (1 << (m - 3 * J + 2)) + low)
        else:
            ok = m2 == k2 - 1 and r2 == 1 + e - V
            z = zero_stretches(r2, m2, 1000)
            drops.append((i, J, m, m2 - r2.bit_length(), z[-1] if z else None))
        if not ok: bad += 1; print(f"rebuild {i}: the identity fails")
        if J >= 300: longw.append((i, J, m, [x for x in zero_stretches(r, m, 1000) if x[0] < 3 * J]))
        k, m, r = k2, m2, r2
    print(f"rebuilds 4 .. {R} [{time.time() - t0:.0f} s]: m = k or k - 1 and r' as above at every rebuild "
          f"({bad} failures); largest 3J/m = {worst[0]:.3f} at rebuild {worst[1]}")
    print("drops (V <= e + 1): rebuild, J, m, 0 bits on top of r' after it")
    for d in drops: print("  ", d[:4])
    print("words of 300 groups or more: rebuild, J, m, the stretches of >= 1000 zeros the word reads (position, length)")
    for w in longw: print("  ", w)
    sys.exit(1 if bad else 0)


def kmin(w, low, z):
    """the least K such that the transient of the low bits w gives the J and e of a long list for every list
    length k from K to 3z + 40 (scanning down from 3z + 40 to the first k that does not)"""
    m = low + 1; r = w | (1 << low)
    ref = rm.word(4 * low // 3 + 24, m, r)
    if not isinstance(ref[0], int): return None
    for kk in range(3 * z + 40, -1, -1):
        a = rm.word(kk, m, r)
        if not (isinstance(a[0], int) and a[:2] == ref[:2]): return ref[0], kk + 1
    return ref[0], 0


def lists(N):
    random.seed(4); worst = worstJ = None; n = 0; t0 = time.time()
    while n < N:
        z = random.choice([0, 0, 1, 2, 5, 10, 20]); low = 150
        w = random.getrandbits(low - 3 * z) << (3 * z)
        if (w >> (3 * z)) & 7 == 0: continue
        J = rm.auto_J(w, low // 3)
        if J is None or 3 * J + 6 > low: continue
        res = kmin(w, low, z)
        if res is None: continue
        n += 1; d = res[1] - 3 * z; dJ = res[1] - 3 * res[0]
        if worst is None or d > worst[0]: worst = (d, z, res[0])
        if worstJ is None or dJ > worstJ[0]: worstJ = (dJ, z, res[0])
    print(f"{N} random words [{time.time() - t0:.0f} s]: every list of at least 3z + {worst[0]} works "
          f"(z = {worst[1]}, J = {worst[2]}); every list of at least 3J {worstJ[0]:+d} works "
          f"(z = {worstJ[1]}, J = {worstJ[2]})")


if __name__ == "__main__":
    {"run": lambda: run(int(sys.argv[2])), "list": lambda: lists(int(sys.argv[2]))}[sys.argv[1]]()
