"""Plant a loop state whose two countdowns let the loop carry the right end almost to the end of a small tape,
then follow it in the mark model."""
import sys
from conc import Model
def v2(x):
    if x == 0: return 99
    c = 0
    while x % 2 == 0: x //= 2; c += 1
    return c
def run(a, b, c, E, rounds=60, verbose=True):
    m = Model(1); m.W = m.const(E)
    for v in (a, b, c): m.add('W', m.const(v))
    m.add('G', m.const(1))
    out = []
    for r in range(rounds):
        ne = len(m.endd)
        m.do_round()
        sh = m.shape()
        ds = [d.v for (rr, d) in m.endd[ne:]]
        out.append((sh, ds, m.bad, m.halted))
        if verbose: print(f"  round {r+1:2d}: {sh:10s} end meetings d = {ds}  (end at {m.W.v})" + (f"  BAD {m.bad}" if m.bad else "") + ("  HALT" if m.halted else ""))
        if m.bad or m.halted: break
        mk = m.marks()
        if len(mk) == 2 and mk[1][0] == 'M' and mk[1][1].v == m.W.v - 2: print("  clean tape"); break
    return out
if __name__ == '__main__':
    E0 = int(sys.argv[1]); passes = int(sys.argv[2]); kR = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    best = None
    for E in range(E0, E0 + 4000, 4):
        R = kR << (4 * passes + 1)
        c = E - 1 - R
        if c % 2 == 0: continue
        a = (int(E * 0.15)) | 1
        # 147 b = 578 + 392 c - 280 E  (mod 2^(6 passes + 1))
        M = 1 << (6 * passes + 1)
        b0 = ((578 + 392 * c - 280 * E) * pow(147, -1, M)) % M
        target = int(E * 0.65)
        b = b0 + M * ((target - b0) // M)
        if b < a + 10: b += M
        if b % 2: continue
        if not (a < b < c): continue
        L1 = 147 * b + 280 * E - 392 * c - 578
        print(f"E = {E}, a = {a}, b = {b}, c = {c}: R = {E - c - 1} (v2 {v2(E - c - 1)}), L1 = {L1} (v2 {v2(L1)})")
        run(a, b, c, E)
        break
