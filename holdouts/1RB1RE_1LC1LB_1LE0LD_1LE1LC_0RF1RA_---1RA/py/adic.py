"""The 3/2 counter of 1RB1RE_1LC1LB_1LE0LD_1LE1LC_0RF1RA_---1RA, computed 2-adically, far past 260,000 epochs.

An epoch goes from the visit [6, 4, u^m, L] to the next visit [6, 4, u^m', L'].  For m large (py/adversary.py) the
stack L' and the offset c in

    m' = (3m + c) / 2

depend only on L and on p = m mod 2 (and c = p mod 2).  So the run of the machine is a pair of sequences: the
parities p_0 p_1 p_2 ... of the counter, and the stacks they drive.  Two facts make a long run cheap:

* The stack: an epoch changes only the top few entries of L.  `epoch` runs the exact run-stack simulator
  (py/runstack.py) on the top K entries of L only, with the counter replaced by BIG + p, and doubles K until the
  head provably stayed above the cut (the bottom entry of the cut copy is never reached).  The counter of the real
  run is astronomically larger than BIG after the first epochs; `epoch` is checked at a second size (BIG2) every
  CHECK epochs, and the whole method against the exact simulator in `check`.
* The counter: the parity of m_i is a function of m_0 mod 2^(i+1) alone (3 is a unit mod 2), so the next B
  parities need only the low B bits of m.  `run` keeps m exactly but touches all of it only once per block of B
  epochs:  2^B m_B = 3^B m_0 + C_B,  C_(i+1) = 3 C_i + 2^i c_i.  Inside a block it works on m mod 2^(B-i).

usage: python3 adic.py check N        N epochs both ways (fast method and py/visit.py's exact simulator): the same
                                      parities, stacks and counters (N = 20000 takes about a minute)
       python3 adic.py run N [OUT]    N epochs with the fast method; statistics; optionally a JSON summary
"""
import sys, os, time, json, collections, math
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from runstack import Sim, B as STATE_B

BIG = 2 ** 64 + 2 ** 33          # stand-in for the counter (even; the parity is added)
BIG2 = 2 ** 40 + 2 ** 21
CHECK = 1000
E0 = 2000                        # epochs of the exact simulator before the fast method takes over
BLOCK = 4096


def is_start(R):
    return len(R) >= 3 and R[-1] == [6, 1] and R[-2] == [4, 1] and R[-3][0] == 1


def epoch(sub, p, big=BIG):
    """sub: top entries of the stack L, bottom first (as in Sim.R), as lists [run, count].
    One epoch from [6, 4, u^(big+p), sub].  Returns (sub', c, depth, minlen) or ('HALT', ...):
    depth = entries of L the head passed (as py/visit.py counts), minlen = fewest entries left of sub below the head."""
    s = Sim(); s.st = STATE_B; s.d = -1
    s.R = sub + [[1, big + p], [4, 1], [6, 1]]
    start = len(sub); minR = start; minlen = len(s.R); first = True; n = 0
    while True:
        if s.at_visit():
            R = s.R
            if not first and is_start(R) and R[-3][1] > big:
                m2 = R[-3][1]
                return R[:-3], 2 * m2 - 3 * (big + p), start - minR, minlen
            first = False
            s.sweep()
        if not s.step(): return 'HALT', None, start - minR, minlen
        lr = len(s.R)
        if lr < minlen: minlen = lr
        if s.d == 1 and lr < minR: minR = lr
        n += 1
        if n > 10 ** 7: raise RuntimeError("epoch did not end")


def exact_start(NE):
    """the exact run from blank tape up to the start of epoch NE: (R, m, steps) with R the stack L bottom first"""
    s = Sim(); ne = 0
    while True:
        if s.at_visit():
            if is_start(s.R):
                ne += 1
                if ne == NE:
                    R = s.R
                    return [list(e) for e in R[:-3]], R[-3][1], s.steps
            s.sweep()
        if not s.step(): raise RuntimeError("HALT at step %d" % (s.steps + 1))


def advance(R, p, stats, ne):
    """one epoch of the stack R (modified in place); returns c"""
    K = 8
    while True:
        K = min(K, len(R))
        sub = [list(e) for e in R[len(R) - K:]]
        r = epoch(sub, p)
        if r[0] == 'HALT':
            if K == len(R): raise SystemExit("HALT at epoch %d (parity %d)" % (ne, p))
        elif r[3] >= 2 or K == len(R):
            break
        K *= 2
    new, c, depth, minlen = r
    if ne % CHECK == 0:
        sub2 = [list(e) for e in R[len(R) - K:]]
        r2 = epoch(sub2, p, BIG2)
        assert r2[0] == new and r2[1] == c, "epoch map depends on the counter's size at epoch %d" % ne
    stats['drun'] = sum(e[1] for e in new) - sum(e[1] for e in R[len(R) - K:])
    R[len(R) - K:] = new
    stats['depth'][depth] += 1
    stats['K'][K] += 1
    return c


def fast(NE, R, m, ne0, report=None, series=None):
    """from the start of epoch ne0 with stack R, counter m: run up to the start of epoch NE.
    Returns (R, m, stats, parities as a bytearray); appends the number of runs of each stack to `series`."""
    stats = {'depth': collections.Counter(), 'K': collections.Counter(), 'minstack': [], 'maxdepth': []}
    par = bytearray(); ne = ne0; t0 = time.time()
    while ne < NE:
        Bk = min(BLOCK, NE - ne)
        x = m & ((1 << Bk) - 1); C = 0
        for i in range(Bk):
            p = x & 1; par.append(p)
            c = advance(R, p, stats, ne)
            if series is not None: series.append(series[-1] + stats['drun'])
            C = 3 * C + (c << i)
            x = ((3 * x + c) >> 1) & ((1 << (Bk - 1 - i)) - 1) if i < Bk - 1 else 0
            ne += 1
            if ne % 100000 == 0:
                stats['minstack'].append(len(R))
        num = pow(3, Bk) * m + C
        assert num & ((1 << Bk) - 1) == 0
        m = num >> Bk
        if report and ne % report < BLOCK:
            print("epoch %d: counter of %d bits, stack %d entries (%d runs), %.0f s" %
                  (ne, m.bit_length(), len(R), sum(e[1] for e in R), time.time() - t0), flush=True)
    return R, m, stats, par


def check(N):
    R, m, steps = exact_start(E0)
    Rf, mf, stats, par = fast(N, [list(e) for e in R], m, E0)
    # exact: continue the full simulator from blank tape to epoch N and record the parities on the way
    s = Sim(); ne = 0; epar = bytearray(); t0 = time.time()
    while True:
        if s.at_visit():
            if is_start(s.R):
                ne += 1
                if ne == N: break
                if ne >= E0: epar.append(s.R[-3][1] & 1)
            s.sweep()
        if not s.step(): raise RuntimeError("HALT")
    Rx, mx = [list(e) for e in s.R[:-3]], s.R[-3][1]
    assert epar == par, "parities differ"
    assert Rx == Rf, "stacks differ"
    assert mx == mf, "counters differ"
    print("epochs %d..%d: fast method = exact simulator (parities, stack of %d entries, counter of %d bits); %.0f s"
          % (E0, N, len(Rx), mx.bit_length(), time.time() - t0))


def run(N, out=None):
    t0 = time.time()
    R, m, steps = exact_start(E0)
    R, m, stats, par = fast(N, R, m, E0, report=max(BLOCK, N // 20))
    runs = sum(e[1] for e in R)
    lg = m.bit_length() - 1 + math.log2(m >> (m.bit_length() - 53)) - 52
    # every epoch makes at least m/2 sweeps from X = 6: more than 1.5 m^2 - m steps (README); a lower bound
    low10 = (2 * lg + math.log2(1.5)) * math.log10(2)
    print("epochs %d: no halt | counter m has %d bits | stack %d entries, %d runs | more than 10^%d steps | %.0f s"
          % (N, m.bit_length(), len(R), runs, int(low10), time.time() - t0))
    tot = sum(stats['depth'].values())
    print("entries of the stack passed by the head in one epoch (epochs %d..%d):" % (E0, N))
    for k in sorted(stats['depth']): print("  %d: %d (%.2e)" % (k, stats['depth'][k], stats['depth'][k] / tot))
    ones = sum(par)
    print("parities: %d odd of %d (%.5f)" % (ones, len(par), ones / len(par)))
    longest = max(len(t) for t in bytes(par).split(b'\x00'))
    longest0 = max(len(t) for t in bytes(par).split(b'\x01'))
    print("longest run of odd epochs %d, of even epochs %d" % (longest, longest0))
    if out:
        json.dump({'epochs': N, 'counter_bits': m.bit_length(), 'counter_low64': m & (2 ** 64 - 1),
                   'stack_entries': len(R), 'stack_runs': runs, 'log10_steps_lower': int(low10),
                   'depth': dict(sorted(stats['depth'].items())), 'odd': ones, 'longest_odd': longest,
                   'longest_even': longest0, 'stack_top': R[-12:], 'stack_bottom': R[:12],
                   'stack_every_1e5': stats['minstack']}, open(out, 'w'))
        with open(out + '.par', 'wb') as fh: fh.write(bytes(par))


if __name__ == "__main__":
    mode = sys.argv[1]; n = int(float(sys.argv[2]))
    if mode == 'check': check(n)
    else: run(n, sys.argv[3] if len(sys.argv) > 3 else None)
