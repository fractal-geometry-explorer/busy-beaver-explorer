"""Accelerated exact simulator: `bbtools.macro` (blocks of K cells, whole runs crossed at once) plus jumps over
repeated periods of bounces.

Each time the head turns from moving left to moving right (at the left end of the tape only, with `--bounce L`),
the run-length tape is recorded.  When the last three records p turns apart (p <= P) have the same blocks and the
run counts change by the same vector d from one to the next, and the head position too, the period is repeated k
times at once: counts += k d, steps += the sum of the k period lengths (they grow by a constant, since a period's
length is linear in the counts), with k the largest number that keeps every decreasing count >= MARGIN.  Between
two equal records the machine touched each run only at its ends (a run crossed whole in one macro step looks the
same to it whatever its length), so with all runs long enough the next period does the same again; MARGIN leaves
room for the cells a period takes from a run's end.  The jumps are not proved here: `--hash` prints a hash of the
tape at given step counts (the first macro-step boundary at or after each), to compare with `c/tapehash.c`, which
runs the plain machine.

usage: python3 accel.py MACHINE K BOUNCE STEPS [--events] [--hash S1 S2 ...] [--time SECONDS]
  K       block size of the macro machine (2 for 1RB1RC_..., 4 for 1RB1LF_...)
  BOUNCE  L: record only turns at the left end; A: every left-to-right turn
  --events  print the run-length tape each time the visited tape grows on the right (in blocks of K cells)
"""
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "..", "tools", "py"))
from bbtools.macro import MacroRun  # noqa: E402

MARGIN = 8


class Accel:
    def __init__(self, machine, k=2, P=40, bounce="L"):
        self.r = MacroRun(machine, k)
        self.P, self.bounce_side = P, bounce
        self.hist = []
        self.minpos = self.maxpos = 0
        self.jumps = 0

    def snap(self):
        r = self.r
        sig = (r.state, r.dir, tuple(b for b, _ in r.left), tuple(b for b, _ in r.right))
        cnt = [c for _, c in r.left] + [c for _, c in r.right]
        return sig, cnt, r.steps, r.pos

    def record(self):
        h = self.hist
        h.append(self.snap())
        if len(h) > 3 * self.P:
            del h[0]
        n = len(h)
        for p in range(1, self.P + 1):
            if 2 * p >= n:
                break
            a, b, c = h[n - 1 - 2 * p], h[n - 1 - p], h[n - 1]
            if not (a[0] == b[0] == c[0]):
                continue
            d1 = [y - x for x, y in zip(a[1], b[1])]
            d2 = [y - x for x, y in zip(b[1], c[1])]
            if d1 != d2 or b[3] - a[3] != c[3] - b[3] or not any(d2):
                continue
            ks = [(x - MARGIN) // -dd for x, dd in zip(c[1], d2) if dd < 0]
            k = min(ks) if ks else 10 ** 6
            if k < 1:
                continue
            c1, c2 = b[2] - a[2], c[2] - b[2]
            self.apply(d2, k, k * c2 + (c2 - c1) * k * (k + 1) // 2, (c[3] - b[3]) * k)
            self.jumps += 1
            self.hist = []
            return

    def apply(self, d, k, dsteps, dpos):
        r = self.r
        L = len(r.left)
        for i, dd in enumerate(d):
            if dd:
                (r.left[i] if i < L else r.right[i - L])[1] += k * dd
        r.steps += dsteps
        r.pos += dpos
        self.minpos, self.maxpos = min(self.minpos, r.pos), max(self.maxpos, r.pos)

    def step(self):
        r = self.r
        d0 = r.dir
        if not r.step():
            return False
        self.minpos, self.maxpos = min(self.minpos, r.pos), max(self.maxpos, r.pos)
        if d0 == -1 and r.dir == 1 and (self.bounce_side == "A" or r.pos <= self.minpos):
            self.record()
        return True

    def tape(self):
        lw, rw = self.r.runs()
        f = lambda ws: " ".join(f"{w}^{c}" if c > 1 else w for w, c in ws)  # noqa: E731
        return f(lw) + " " + "ABCDEF"[self.r.state] + ("> " if self.r.dir == 1 else "< ") + f(rw)


def tape_hash(r):
    """FNV-1a (64 bit) of the tape between its outermost 1s, as c/tapehash.c computes it."""
    c = r.cells()
    ones = [p for p, v in c.items() if v]
    h = 0xcbf29ce484222325
    for p in range(min(ones), max(ones) + 1):
        h ^= 48 + c.get(p, 0)
        h = (h * 0x100000001b3) & 0xFFFFFFFFFFFFFFFF
    return f"{h:016x} {max(ones) - min(ones) + 1}"


def main(argv):
    if len(argv) < 4:
        sys.exit(__doc__)
    machine, k, side, steps = argv[0], int(argv[1]), argv[2], float(argv[3])
    events = "--events" in argv
    hashes = []
    if "--hash" in argv:
        i = argv.index("--hash") + 1
        while i < len(argv) and not argv[i].startswith("--"):
            hashes.append(int(float(argv[i])))
            i += 1
    tl = float(argv[argv.index("--time") + 1]) if "--time" in argv else 1e18
    A = Accel(machine, k, bounce=side)
    r, t0, nxt, mx = A.r, time.time(), 10.0, 0
    while r.steps < steps and time.time() - t0 < tl:
        if not A.step():
            print(f"HALT after {r.steps} steps: {A.tape()}")
            return
        if events and A.maxpos > mx:
            mx = A.maxpos
            print(f"{r.steps} width={A.maxpos - A.minpos} {A.tape()}", flush=True)
        while hashes and r.steps >= hashes[0]:
            hashes.pop(0)
            print(f"hash {r.steps} {'ABCDEF'[r.state]} {tape_hash(r)}", flush=True)
        if r.steps >= nxt:
            print(f"# {r.steps:.3e} steps, {r.msteps} macro steps, {A.jumps} jumps, "
                  f"{len(r.left) + len(r.right)} runs, width {(A.maxpos - A.minpos) * 1}, "
                  f"{time.time() - t0:.0f} s", flush=True)
            nxt *= 10
    print(f"# stopped at {r.steps} steps ({r.steps:.3e}), no halt; {A.jumps} jumps")


if __name__ == "__main__":
    main(sys.argv[1:])
