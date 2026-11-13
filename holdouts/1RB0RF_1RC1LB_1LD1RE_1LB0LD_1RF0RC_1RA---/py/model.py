"""The macro model of 1RB0RF_1RC1LB_1LD1RE_1LB0LD_1RF0RC_1RA---: its checks and a run rebuild by rebuild.

The same model as for 1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE--- (see py/model.py there), in another coding.

Configurations.  At the moments the head is in C on a 0 just right of a 1, the tape is, in the run from blank tape,

    1^b0 0 1^b1 0 ... 0 1^bk 0 1 0 1^l  C>  0^g1 1 0^g2 1 ... 0^gr 1  0^inf     (g1 counts the head's cell)

a list of blocks b0 .. bk (the *interior*), one block of a single 1, a last block l, and a *zone* of single 1s.  The
configuration is *regular* if k >= 1, b0 is even, b1 .. bk are odd, l is a positive multiple of 5, g1 is a positive
multiple of 5 and the other gaps are 4 mod 5.  A *sub-round* runs from one such moment to the next.

The model (observed; checked by `check` and `rounds`; not proved):

  W      the interior changes by one step W:  (..., x, 2a + 1)  ->  (..., x + 2, 1, 1, ..., 1)   (a blocks of 1).
         With digits a_i = (b_i - 1) / 2 this is: remove the last digit a, add 1 to the one before, append a zeros.
  zone   l and the zone are a binary counter.  Write s1 = g1 and s_i = g_i + 1 (all multiples of 5).  If l > 5 the
         next state is l = 5 with a new first segment l - 5.  If l = 5, all leading segments equal to 5 are removed
         (n of them), the next segment loses 5 cells (blank tape gives them if there is no next segment) and
         l = 5 n + 10.  So l + s1 + s2 + ... = 5 (m + 1) stays fixed for 2^m sub-rounds (a *round*), then m grows by 1.
  T      a tail (..., q, a) becomes (..., q + a + 1) after exactly 2^a steps of W, so an interior with digits
         a_1 .. a_k is a single block after T = sum over i of 2^(a_i + ... + a_k + k - i) steps.
  rebuild  with a single block left the sub-rounds are irregular for a while (the *transient*), then regular again
         with a longer list.  No rule is known for the transient; `run` gives it to the machine (c/trans.c).

`run` alternates arithmetic (W steps and counter steps, any number at once, while the interior and the near zone are
regular) with direct simulation.  A halt can only be found by the direct part; "no halt" rests on the arithmetic part,
which is checked but not proved.  Some transients contain a second kind of regular stretch (observed, not modelled):
the block before l is 2 l / 5 + 1 instead of 1, the list counts the sub-rounds upwards in binary, and a gap of the
zone of 5 q + 4 cells is used up in about 2^(q+1) sub-rounds.  `run` simulates these cell by cell (q = 24 in the
1504th transient) and is stuck after rebuild 3792 at one that is too long.

usage: python3 model.py check N         N sub-rounds after step 1399, machine against model, one by one (pure Python)
       python3 model.py partial         W steps and counter steps taken many at once against the machine
       python3 model.py rounds          the lists at 6 round ends after the first rebuild against a direct run
       python3 model.py run K [SECONDS] K rebuilds of the hybrid run (stops after SECONDS)
"""
import os, sys, time, subprocess, tempfile
sys.set_int_max_str_digits(0)
HERE = os.path.dirname(os.path.abspath(__file__))
M = "1RB0RF_1RC1LB_1LD1RE_1LB0LD_1RF0RC_1RA---"
PP, QQ, UU, L0, AUX = 2, 1, 5, 5, 1        # block coding 2a + 1, counter unit 5, smallest last block 5, one extra block 1
START_STEP = 1399
START = ([2, 1, 1, 1, 1, 7, 1, 1, 5], 15, [])     # interior, l, gaps at step 1399 from blank tape (`check` verifies it)
# `tmrun MACHINE 20000000000 at C R 2000` (tools/c/tmrun.c, 1 minute): step, interior, l at the ends of rounds
DIRECT_REBUILDS = 1
DIRECT = [(335864993, "2 1^7 3 1^3 7 1^10 7 3 1^4", 120), (671409304, "2 1^7 3 1^2 9 1^10 7 3 1^4", 125),
          (1342497935, "2 1^7 3 1 11 1^10 7 3 1^4", 130), (2684675206, "2 1^7 3 13 1^10 7 3 1^4", 135),
          (5369029757, "2 1^7 17 1^10 7 3 1^4", 140), (10737738872, "2 1^6 3 15 1^10 7 3 1^4", 145)]


def table(m):
    T = {}
    for s, row in enumerate(m.split("_")):
        for b in (0, 1):
            t = row[3 * b:3 * b + 3]
            T[(s, b)] = None if t[0] == "-" else (int(t[0]), 1 if t[1] == "R" else -1, ord(t[2]) - 65)
    return T


TAB = table(M)


def rle(I):
    out = []
    for b in I:
        if out and out[-1][0] == b: out[-1][1] += 1
        else: out.append([b, 1])
    return " ".join(f"{b}^{n}" if n > 1 else str(b) for b, n in out)


# ---------------------------------------------------------------- the machine, in Python (small cases)
def read(tape, head):
    """(blocks, gaps) if the tape is a block word left of the head, else None; gaps: the runs of 0s before each 1
    right of the head (0 between two 1s side by side)"""
    ones = [k for k, v in tape.items() if v]
    if not ones: return None
    left = "".join(str(tape.get(i, 0)) for i in range(min(ones), head))
    right = "".join(str(tape.get(i, 0)) for i in range(head, max(ones) + 1))
    if "00" in left or not left.endswith("1"): return None
    return [len(x) for x in left.split("0")], ([len(x) for x in right.split("1")[:-1]] if right else [])


def sub_round(blocks, gaps, maxsteps=10 ** 7):
    """one sub-round of the machine from the configuration (blocks incl. l, gaps): ("ok", steps, (blocks, gaps))"""
    tape = {}; pos = 0
    for i, b in enumerate(blocks):
        for _ in range(b): tape[pos] = 1; pos += 1
        if i < len(blocks) - 1: pos += 1
    head = pos; p = pos
    for g in gaps: p += g; tape[p] = 1; p += 1
    st = 2
    for n in range(1, maxsteps + 1):
        t = TAB[(st, tape.get(head, 0))]
        if t is None: return "HALT", n, None
        tape[head] = t[0]; head += t[1]; st = t[2]
        if st == 2 and tape.get(head, 0) == 0 and tape.get(head - 1, 0) == 1:
            r = read(tape, head)
            if r: return "ok", n, r
    return "max", maxsteps, None


# ---------------------------------------------------------------- the model
def enc(m, rem):
    """(l, segments) of the counter in round m with rem sub-rounds left (1 <= rem <= 2^m)"""
    tz = (rem & -rem).bit_length() - 1; l = L0 + UU * tz; segs = []
    for i in range(tz, m):
        if i == tz or not (rem >> i) & 1: segs.append(UU)
        else: segs[-1] += UU
    return l, segs


def dec(l, segs):
    m = (l + sum(segs) - L0) // UU; tz = (l - L0) // UU; rem = 0; pos = tz
    if not segs: return m, 1 << m
    for k, s in enumerate(segs):
        n = s // UU
        if k == 0: rem |= ((1 << n) - 1) << pos
        else: rem |= ((1 << (n - 1)) - 1) << (pos + 1)
        pos += n
    assert pos == m
    return m, rem


def W(I):
    a = (I[-1] - QQ) // PP
    return I[:-2] + [I[-2] + PP] + [QQ] * a


def counter(l, segs):
    if l > L0: return L0, [l - L0] + segs
    segs = list(segs); n = 0
    while segs and segs[0] == UU: segs.pop(0); n += 1
    if segs: segs[0] -= UU
    return L0 + UU * (n + 1), segs


def regular_interior(I):
    return len(I) >= 2 and I[0] % PP == 0 and all(b % PP == QQ for b in I[1:])


def regular_last(l):
    return l >= L0 and (l - L0) % UU == 0


def collapse_T(I):
    s = -1; T = 0
    for b in reversed(I[1:]):
        s += (b - QQ) // PP + 1; T += 1 << s
    return T


def applyW(I, n):
    """W^n(I), n <= collapse_T(I), in time polynomial in the length of I and of n"""
    I = list(I)
    while n > 0:
        a = (I[-1] - QQ) // PP
        if n >= (1 << a):
            n -= 1 << a; b = I.pop(); I[-1] += b + 1
        else:
            n -= 1; I.pop(); I[-1] += PP
            if a >= 1:
                k = min(a, (n + 1).bit_length())         # k zeros merge into one digit k - 1 in 2^(k-1) - 1 steps
                I.extend([QQ] * (a - k)); I.append(PP * (k - 1) + QQ); n -= (1 << (k - 1)) - 1
    return I


def split(gaps):
    """(regular leading segments, the other gaps, whether the whole zone is regular)"""
    segs = []
    for i, g in enumerate(gaps):
        s = g if i == 0 else g + 1
        if s % UU or s < UU: return segs, gaps[i:], False
        segs.append(s)
    return segs, [], True


def to_gaps(segs, rest=()):
    return segs[:1] + [s - 1 for s in segs[1:]] + list(rest)


def jump(I, l, gaps):
    """as many regular sub-rounds as the model allows at once: (I, l, gaps, number of sub-rounds)"""
    segs, rest, full = split(gaps)
    if not (regular_interior(I) and regular_last(l) and (full or segs)): return I, l, gaps, 0
    T = collapse_T(I); m, rem = dec(l, segs)
    if full:
        n = T; G = (1 << (m + 1)) - rem + n; m = G.bit_length() - 1; l, segs = enc(m, (1 << (m + 1)) - G)
    else:
        n = min(T, rem - 1); l, segs = enc(m, rem - n)
    return applyW(I, n), l, to_gaps(segs, rest), n


# ---------------------------------------------------------------- the machine, in C
_BIN = None


def trans(I, l, gaps, R=40, maxsteps=10 ** 11):
    global _BIN
    if _BIN is None:
        _BIN = os.path.join(tempfile.mkdtemp(), "trans")
        subprocess.run(["gcc", "-O2", "-o", _BIN, os.path.join(HERE, "..", "c", "trans.c")], check=True)
    inp = " ".join(map(str, I + ([AUX] if AUX else []) + [l])) + "\n" + " ".join(map(str, gaps)) + "\n"
    out = subprocess.run([_BIN, M, str(maxsteps), repr(float(R))] + [str(x) for x in (PP, QQ, UU, L0, AUX)],
                         input=inp, capture_output=True, text=True).stdout.split("\n")
    h = out[0].split()
    if h[0] not in ("reg", "part"): return h[0], int(h[1]), None, None, None
    a, b, c = out[1].split("|"); I = [int(x) for x in a.split()]
    if AUX: assert I.pop() == AUX
    return h[0], int(h[1]), I, int(b), [int(x) for x in c.split()]


def run(I, l, gaps, K, tmax=1e18, verbose=True, R=40, maxsteps=10 ** 11):
    """the hybrid run: ("ok" | "HALT" | "max", rebuilds, sub-rounds jumped, steps simulated directly)"""
    t0 = time.time(); nreb = 0; subs = 0; dsteps = 0; calls = 0
    while nreb < K and time.time() - t0 < tmax:
        I, l, gaps, n = jump(I, l, gaps); subs += n
        if n and len(I) == 1:
            nreb += 1
            if verbose:
                print(f"rebuild {nreb}: single block {I[0]}, l = {l}, zone {gaps[:5]}{'...' if len(gaps) > 5 else ''}; "
                      f"more than 2^{subs.bit_length() - 1} sub-rounds so far; {dsteps} steps simulated directly "
                      f"in {calls} calls [{time.time() - t0:.0f} s]", flush=True)
        r = trans(I, l, gaps, R, maxsteps); calls += 1
        if r[0] not in ("reg", "part"):
            print(f"{r[0]} after {r[1]} steps from the configuration {rle(I)[:300]} | {l} | {gaps[:12]}")
            return r[0], nreb, subs, dsteps
        dsteps += r[1]; I, l, gaps = r[2], r[3], r[4]
    return "ok", nreb, subs, dsteps


# ---------------------------------------------------------------- commands
def unpack(bl):
    """(interior, l) of a list of blocks; with AUX the block before l is not part of the interior"""
    if AUX: return (bl[:-2], bl[-1]) if len(bl) >= 2 and bl[-2] == AUX else ([], bl[-1])
    return bl[:-1], bl[-1]


def pack(I, l):
    return I + ([AUX] if AUX else []) + [l]


def blank_start():
    tape = {}; head = 0; st = 0
    for _ in range(START_STEP):
        t = TAB[(st, tape.get(head, 0))]; tape[head] = t[0]; head += t[1]; st = t[2]
    assert st == 2 and tape.get(head, 0) == 0
    return read(tape, head)


def main():
    cmd = sys.argv[1]
    if cmd == "check":
        N = int(sys.argv[2]); bl, gp = blank_start()
        assert (*unpack(bl), gp) == START, (bl, gp)
        print(f"step {START_STEP} from blank tape: interior {rle(START[0])}, l = {START[1]}, zone {START[2]}")
        exc = []; steps = START_STEP; singles = []
        for i in range(N):
            I, l = unpack(bl)
            pred = None
            segs, rest, full = split(gp)
            if regular_interior(I) and regular_last(l) and full:
                l2, s2 = counter(l, segs); pred = (pack(W(I), l2), to_gaps(s2))
            if len(I) == 1 and I[0] % PP == 0: singles.append((i, I[0], l, list(gp)))
            r = sub_round(bl, gp)
            if r[0] != "ok": print("sub-round", i, r[0], "at step", steps + r[1]); sys.exit(1)
            steps += r[1]; bl, gp = r[2]
            if pred is None: exc.append(i)
            elif pred != (bl, gp): print("the model is wrong at sub-round", i); sys.exit(1)
        runs = []
        for i in exc:
            if runs and runs[-1][1] == i - 1: runs[-1][1] = i
            else: runs.append([i, i])
        print(f"{N} sub-rounds ({steps - START_STEP} steps): {N - len(exc)} regular ones all follow the model; "
              f"{len(exc)} are not regular, in {len(runs)} stretches: {[tuple(r) for r in runs]}")
        ok = True
        # the time to the next rebuild, predicted from the list at the end of each transient
        for a, b in runs:
            print(f"  sub-round {a}: single block" if any(s[0] == a for s in singles) else f"  sub-round {a}: (no single block)")
        bl, gp = blank_start(); I, l = unpack(bl); pred_at = []
        I2, l2, g2, n = jump(I, l, gp); pred_at.append(n)
        for (a, b), nxt in zip(runs, runs[1:] + [None]):
            ok &= pred_at[-1] == a
            if nxt is None: break
            # state after the transient: replay it with the machine
            cur = (pack(I2, l2), g2)
            for _ in range(b - a + 1): cur = sub_round(*cur)[2]
            I2, l2, g2, n = jump(*unpack(cur[0]), cur[1]); pred_at.append(b + 1 + n)
        print("  sub-rounds at which the model predicts a single block:", pred_at, "(matches)" if ok else "(DIFFERENT)")
        sys.exit(0 if ok else 1)
    if cmd == "partial":
        I, l, gaps = START; bad = tested = 0
        for k in range(11):
            I, l, gaps, n = jump(I, l, gaps); J, lj, gj = I, l, gaps
            for _ in range(60):
                r = trans(J, lj, gj, 3)
                if r[0] != "part": break
                J, lj, gj = r[2], r[3], r[4]
                J2, l2, g2, n2 = jump(J, lj, gj)
                if n2 <= 400:
                    cur = (pack(J, lj), list(gj))
                    for _ in range(n2): cur = sub_round(*cur)[2]
                    tested += 1; bad += (*unpack(cur[0]), cur[1]) != (J2, l2, g2)
                J, lj, gj = J2, l2, g2
            r = trans(I, l, gaps, 1e300); I, l, gaps = r[2], r[3], r[4]
        print(f"{tested} jumps of up to 400 sub-rounds with an irregular zone further out, in the transients of the "
              f"first 11 rebuilds: {bad} differ from the machine")
        sys.exit(1 if bad else 0)
    if cmd == "rounds":
        I, l, gaps = START; bad = 0
        for _ in range(DIRECT_REBUILDS):
            I, l, gaps, n = jump(I, l, gaps); r = trans(I, l, gaps, 1e300); I, l, gaps = r[2], r[3], r[4]
        todo = list(DIRECT)
        while todo:
            segs, rest, full = split(gaps); m, rem = dec(l, segs)
            assert full and rem <= collapse_T(I)
            I = applyW(I, rem); l, gaps = L0 + UU * (m + 1), []
            if l < todo[0][2]: continue
            step, want, lw = todo.pop(0)
            same = (rle(I), l) == (want, lw); bad += not same
            print(f"  end of round {m}: {rle(I)} | {l}   direct run at step {step}: {'the same' if same else 'DIFFERENT'}")
        sys.exit(1 if bad else 0)
    if cmd == "run":
        K = int(sys.argv[2]); tmax = float(sys.argv[3]) if len(sys.argv) > 3 else 1e18
        st, nreb, subs, dsteps = run(*START, K, tmax)
        print(f"{st}: {nreb} rebuilds, more than 2^{subs.bit_length() - 1} sub-rounds (so more than that many steps), "
              f"{dsteps} steps simulated directly")


if __name__ == "__main__":
    main()
