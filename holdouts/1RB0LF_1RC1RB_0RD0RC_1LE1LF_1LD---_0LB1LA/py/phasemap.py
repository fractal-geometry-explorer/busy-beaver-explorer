"""Phase map of 1RB0LF_1RC1RB_0RD0RC_1LE1LF_1LD---_0LB1LA, run exactly from blank tape, phase after phase.

Sample tape: `w 1^K 0^Z` with C on the last 0 (once a sweep).  `w` is the counter (a few hundred to a few thousand
cells), 1^K the long block, 0^Z the cells the block has given back.

* One sweep (`sweep`): the head leaves the counter, crosses the block and the blank tape and comes back
  (lean/Passes.lean, for every K and Z), so a sweep can be run on `w 1^K0 0^Z0` with K0 = 32 + K mod 4 and
  Z0 = 32 + Z mod 4 and lifted: w' is the same, K and Z move by the same amounts, and the step count is
  dt0 + 6 (K - K0) + 2 (Z - Z0).
* Many sweeps (`run`): a sweep only reads the right end of the counter, up to the deepest carry.  If a run of
  sweeps stays inside a suffix v of w, its effect depends on v alone; `run` caches (v -> sweeps until a sweep
  reaches left of v) and builds long runs from short ones, as an odometer does.
* Phase change: when K is used up (K < 80 here) the sweeps are run one at a time with K exact; the sweep in which
  the zeros become the new block is run on Z0 = 32 + Z mod 4, Z0 + 8 and Z0 + 16 to check it is linear in Z.

A phase starts at the sweep where K jumps (the zeros became the block, Z = 1).  K' = 2 K + c with c = 2 except at
a few phases.  A halt anywhere is detected (raises Halt): every sweep the cache holds was run once for real.

usage: python3 py/phasemap.py N [--log FILE] [--ckpt FILE]       run to phase N, one line per phase; FILE.log gets
                                                                   n, t, K, Z, c (and w every 100 phases), --ckpt
                                                                   keeps the last phase start and resumes from it
       python3 py/phasemap.py --check                             compare with a direct run to 3·10^9 steps
"""
import ctypes
import itertools
import json
import os
import subprocess
import sys
import time

sys.setrecursionlimit(1000000)
HERE = os.path.dirname(os.path.abspath(__file__))
M = "1RB0LF_1RC1RB_0RD0RC_1LE1LF_1LD---_0LB1LA"
# (write, move, next) for state*2+read; states A..F = 0..5; E reading 1 is the halt
TB = [(1, 1, 1), (0, -1, 5), (1, 1, 2), (1, 1, 1), (0, 1, 3), (0, 1, 2),
      (1, -1, 4), (1, -1, 5), (1, -1, 3), None, (0, -1, 1), (1, -1, 0)]
B0 = 32     # reduced block lengths: B0 + (K mod 4), B0 + (Z mod 4)
TH = 80     # below this K the sweeps are run one at a time
PAD = 6     # zeros kept left of the counter, so a carry that grows it stays inside


class Halt(Exception):
    pass


_lib = None


def _load_c():
    global _lib
    src = os.path.join(HERE, "../c/sweep.c")
    so = os.path.join(os.environ.get("TMPDIR", "/tmp"), "sweep116372.so")
    try:
        if not os.path.exists(so) or os.path.getmtime(so) < os.path.getmtime(src):
            subprocess.run(["gcc", "-O2", "-shared", "-fPIC", "-o", so, src], check=True)
        _lib = ctypes.CDLL(so)
        _lib.sweep.restype = ctypes.c_long
    except Exception:
        _lib = None


_load_c()


def raw_sweep(v, K0, Z0, pad):
    """One sweep on 0^pad v 1^K0 0^Z0, C on the last cell.  Returns (lo, v', K', Z', steps), lo the leftmost cell
    visited (pad - lo cells of growth), or None if the head went left of the pad."""
    n = pad + len(v) + K0 + Z0
    buf = bytearray(pad) + bytearray(v) + b"\x01" * K0 + bytearray(Z0 + 64)
    p = n - 1
    if _lib is not None:
        cbuf = (ctypes.c_ubyte * len(buf)).from_buffer(buf)
        lo, hi, hs = ctypes.c_long(), ctypes.c_long(), ctypes.c_long()
        i = _lib.sweep(cbuf, len(buf), p, pad, ctypes.byref(lo), ctypes.byref(hi), ctypes.byref(hs))
        if i == -1:
            raise Halt(f"E reads a 1 {hs.value} steps into a sweep of {bytes(v).hex()} K0={K0} Z0={Z0}")
        if i == -2:
            return None
        if i == -3:
            raise RuntimeError("buffer")
        lo, hi = lo.value, hi.value
        del cbuf
    else:
        t = buf
        hi = p
        lo = pad
        s = 2
        i = 0
        while True:
            r = t[p]
            if i > 0 and s == 2 and r == 0 and p >= hi:
                break
            e = TB[s * 2 + r]
            if e is None:
                raise Halt(f"E reads a 1 {i} steps into a sweep of {bytes(v).hex()} K0={K0} Z0={Z0}")
            t[p] = e[0]
            p += e[1]
            s = e[2]
            i += 1
            if p < lo:
                lo = p
                if p < 0:
                    return None
            if p > hi:
                hi = p
    t = buf
    q = hi
    Z = 0
    K = 0
    while t[q] == 0:
        Z += 1
        q -= 1
    while t[q] == 1:
        K += 1
        q -= 1
    return lo, bytes(t[lo:q + 1]), K, Z, i


# A run of sweeps is summed as (n, D, SD, E, SZ, T, MX): n sweeps; K drops by D in all; SD = sum over the sweeps of
# the drop before each; Z grows by E, SZ the same sum for Z; T = sum of (steps - 6 K0 - 2 Z0); MX the largest drop
# so far (so K never goes below the threshold).  Steps of the run from (K, Z): T + 6 (n K - SD) + 2 (n Z + SZ).
ID = (0, 0, 0, 0, 0, 0, 0)


def cat(a, b):
    n1, D1, SD1, E1, SZ1, T1, M1 = a
    n2, D2, SD2, E2, SZ2, T2, M2 = b
    return (n1 + n2, D1 + D2, SD1 + SD2 + n2 * D1, E1 + E2, SZ1 + SZ2 + n2 * E1, T1 + T2, max(M1, D1 + M2))


memo = {}
BASE = 4
stats = {"sweeps": 0}


def local(v, k, z):
    """One sweep on the suffix v with K = k, Z = z mod 4; None if it reads left of v."""
    stats["sweeps"] += 1
    r = raw_sweep(v, B0 + k, B0 + z, 0)
    if r is None or r[0] != 0:
        return None
    _, vo, K, Z, i = r
    dK = B0 + k - K
    dZ = Z - B0 - z
    return vo, (1, dK, 0, dZ, 0, i - 6 * (B0 + k) - 2 * (B0 + z), max(dK, 0)), (k - dK) % 4, (z + dZ) % 4


def run(v, k, z, budget):
    """Sweeps that stay inside v, until one would read left of v ('esc') or K would drop by more than budget."""
    key = (v, k, z)
    m = memo.get(key)
    if m is not None and m[0][6] <= budget:
        return m + ("esc",)
    acc = ID
    cur = v
    while True:
        if len(cur) > BASE:
            a, b, k, z, why = run(cur[1:], k, z, budget - acc[1])
            acc = cat(acc, a)
            cur = cur[:1] + b
            if why == "budget":
                return acc, cur, k, z, "budget"
        r = local(cur, k, z)
        if r is None:
            memo[key] = (acc, cur, k, z)
            return acc, cur, k, z, "esc"
        vo, a1, k2, z2 = r
        if acc[1] + a1[6] > budget:
            return acc, cur, k, z, "budget"
        acc = cat(acc, a1)
        cur, k, z = vo, k2, z2


def strip(w):
    i = 0
    while i < len(w) and w[i] == 0:
        i += 1
    return w[i:]


def full_sweep(w, K, Z):
    """One sweep from w 1^K 0^Z, any K and Z; returns (w', K', Z', steps)."""
    K0 = K if K < 2 * B0 else B0 + K % 4
    Z0 = Z if Z < 2 * B0 else B0 + Z % 4
    dK, dZ = K - K0, Z - Z0
    lo, vo, K1, Z1, i = raw_sweep(w, K0, Z0, 64)
    if dZ and K1 > K0 + 4:
        # the zeros became the new block: check the sweep is linear in Z
        r2 = raw_sweep(w, K0, Z0 + 8, 64)
        r3 = raw_sweep(w, K0, Z0 + 16, 64)
        if not (dK == 0 and r2[:2] == (lo, vo) and r3[:2] == (lo, vo) and r2[2] == K1 + 8 and r3[2] == K1 + 16
                and r2[3] == Z1 == r3[3] and r3[4] - i == 2 * (r2[4] - i) and (r2[4] - i) % 8 == 0):
            raise RuntimeError(f"phase change not linear in Z at K={K} Z={Z}")
        return strip(vo), K1 + dZ, Z1, i + (r2[4] - i) // 8 * dZ
    return strip(vo), K1 + dK, Z1 + dZ, i + 6 * dK + 2 * dZ


def phases(start=None):
    """Yield (n, t, K, Z, w, c) at the start of each phase: t the step, c = K - 2 K_prev."""
    if start is None:
        n, t, K, Z, w = 0, 2, 2, 1, b""      # step 2 from blank: 1^2 0^1, C on the 0
    else:
        n, t, K, Z, w = start
    Kp = K
    while True:
        if K >= TH:
            acc, ve, _, _, _ = run(bytes(PAD) + w, K % 4, Z % 4, K - TH)
            cnt, D, SD, E, SZ, T, _ = acc
            t += T + 6 * (cnt * K - SD) + 2 * (cnt * Z + SZ)
            K -= D
            Z += E
            w = strip(ve)
        w2, K2, Z2, dt = full_sweep(w, K, Z)
        t += dt
        if Z2 == 1 and K2 > K:
            n += 1
            memo.clear()      # the cache is rebuilt in each phase at no cost in time, and memory stays flat
            yield n, t, K2, Z2, w2, K2 - 2 * Kp
            Kp = K2
        w, K, Z = w2, K2, Z2


def rle(w):
    return " ".join(f"{k}^{len(list(g))}" for k, g in itertools.groupby(w))


def check():
    """Phase starts against a direct run to 3·10^9 steps: the same sweep code on the whole tape (K0 = K, Z0 = Z),
    without the reduction or the cache."""
    n, t, K, Z, w = 0, 2, 2, 1, b""
    direct = []
    while t < 3 * 10 ** 9:
        lo, vo, K2, Z2, i = raw_sweep(w, K, Z, 64)
        t += i
        if Z2 == 1 and K2 > K:
            direct.append((t, K2, rle(strip(vo))))
        w, K, Z = strip(vo), K2, Z2
    fast = []
    for n, t, K, Z, w, c in phases():
        if t >= 3 * 10 ** 9:
            break
        fast.append((t, K, rle(w)))
    ok = fast == direct[:len(fast)] and len(fast) == len(direct)
    for d in direct:
        print(*d)
    print("phase starts:", len(direct), "agree" if ok else "DISAGREE")
    return ok


def main():
    a = sys.argv[1:]
    if a and a[0] == "--check":
        sys.exit(0 if check() else 1)
    N = int(a[0])
    log = a[a.index("--log") + 1] if "--log" in a else None
    ck = a[a.index("--ckpt") + 1] if "--ckpt" in a else None
    start = None
    if ck and os.path.exists(ck):
        d = json.load(open(ck))
        start = (d["n"], d["t"], d["K"], d["Z"], bytes.fromhex(d["w"]))
    f = open(log, "a") if log else None
    t0 = time.time()
    try:
        for n, t, K, Z, w, c in phases(start):
            print(n, c, len(w), t.bit_length(), round(time.time() - t0, 1), rle(w)[-120:], flush=True)
            rec = {"n": n, "t": t, "K": K, "Z": Z, "c": c, "len": len(w)}
            if f:
                f.write(json.dumps(dict(rec, w=w.hex()) if n % 100 == 0 else rec) + "\n")
                f.flush()
            if ck:
                with open(ck + ".tmp", "w") as g:
                    json.dump(dict(rec, w=w.hex()), g)
                os.replace(ck + ".tmp", ck)
            if n >= N:
                break
    except Halt as h:
        print("HALT", h, flush=True)
        if f:
            f.write(json.dumps({"halt": str(h)}) + "\n")


if __name__ == "__main__":
    main()
