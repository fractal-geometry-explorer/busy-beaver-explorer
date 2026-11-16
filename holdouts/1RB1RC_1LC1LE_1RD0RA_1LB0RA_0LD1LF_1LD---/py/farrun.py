"""accel.py's far run for 1RB1RC_1LC1LE_1RD0RA_1LB0RA_0LD1LF_1LD---, resumable from a checkpoint.

The loop is the one of accel.far, unchanged (schedules, closed-form advance to the next event, the event visit by
counters.step); the state (counters, separators, visit count, event log) is pickled every EVERY seconds, so a long
run can be stopped and resumed.

usage:  python3 farrun.py DIGITS SECONDS CKPT       (resumes from CKPT if it exists)
"""
import sys, time, os, pickle
from accel import schedules, advance
from counters import step, Unknown, LAST

EVERY = 600


def save(path, st):
    tmp = path + '.tmp'
    with open(tmp, 'wb') as f:
        pickle.dump(st, f)
    os.replace(tmp, path)


def main(digits, secs, ckpt):
    maxv = 10 ** digits
    if os.path.exists(ckpt):
        with open(ckpt, 'rb') as f:
            cs, ss, v, n_ev, slots, nxt = pickle.load(f)
        print('resumed at visit ~10^%d, m=%d, %d events' % (len(str(v)) - 1, len(cs), n_ev), flush=True)
    else:
        cs, ss, v, n_ev, slots, nxt = [2, 2], ['0'], 1, 0, [], 10
    t0 = time.time(); last = t0
    try:
        while v < maxv and time.time() - t0 < secs:
            decs, over, sf = schedules(cs, ss)
            m = len(cs); T = over
            for k in range(m - 1):
                if cs[k] >= 1:
                    z = decs[k].kth(cs[k])
                    if z is not None and z < T: T = z
                zt = decs[k].kth(cs[k] + 1)
                if zt is not None and zt < T: T = zt
            cs = advance(cs, ss, T, decs)
            ss = [('0' if (sf[k + 1] is not None and sf[k + 1] < T) else s) for k, s in enumerate(ss)]
            v += T
            cs, ss, st, kind = step(cs, ss); v += 1; n_ev += 1
            if kind in ('slot', 'merge'):
                slots.append((v.bit_length(), kind, LAST.get('x'), LAST.get('j'), len(cs)))
            while v >= nxt:
                print('visits >= 10^%d: m=%d, %d events, %d slot/merge, %.0fs' % (len(str(nxt)) - 1, len(cs), n_ev,
                      len(slots), time.time() - t0), flush=True)
                nxt *= 10
            if time.time() - last > EVERY:
                save(ckpt, (cs, ss, v, n_ev, slots, nxt)); last = time.time()
    except Unknown as u:
        print('OUTSIDE THE RULE at visit ~2^%d' % v.bit_length(), u, flush=True)
        return
    save(ckpt, (cs, ss, v, n_ev, slots, nxt))
    print('visits ~2^%d (~10^%d), m=%d, %d events, %.1fs' % (v.bit_length(), len(str(v)) - 1, len(cs), n_ev,
                                                             time.time() - t0))
    xs = [(x, b, j, m) for (b, k, x, j, m) in slots if j is not None and j > 1 and x]
    print('slot/merge rebuilds: %d (%d with x not the first counter)' % (len(slots), len(xs)))
    if xs:
        print('smallest x: %d; sum of 1/x: %.4f; after visit 2^2000: %.2e' % (
            min(x for x, *_ in xs), sum(1 / x for x, *_ in xs), sum(1 / x for x, b, *_ in xs if b > 2000)))
        for x, b, j, m in sorted(xs)[:8]:
            print('  x=%d at visit ~2^%d (index %d of %d)' % (x, b, j, m))


if __name__ == '__main__':
    main(int(sys.argv[1]), float(sys.argv[2]), sys.argv[3])
