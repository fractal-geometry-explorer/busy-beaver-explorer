"""Check the reset map of m2map.py against the machine: for every t < N run from Z(t) = 1^t (head in B on the last 1)
until the next tape of the form 1^t' with B on its last 1 and only 0s around (or a halt), and compare.

usage: python3 check_map.py N"""
import sys
from m2map import G

M = "1RB0LF_1LC1RA_0RE0RD_---1LE_1LF1RC_1LC1LA"
T = {}
for i, g in enumerate(M.split("_")):
    for r in (0, 1):
        t = g[3 * r:3 * r + 3]
        T[(i, r)] = None if t[2] == "-" else (int(t[0]), 1 if t[1] == "R" else -1, ord(t[2]) - 65)


def next_z(t, maxs=10 ** 8):
    """The t' of the next Z(t') after Z(t), or None on a halt."""
    pad = 4 * t + 100
    tape = bytearray(pad) + bytearray([1]) * t + bytearray(pad)
    h, st, lo, hi, n = pad + t - 1, 1, pad, pad + t - 1, 0
    while n < maxs:
        tr = T[(st, tape[h])]
        if tr is None:
            return None
        w, d, s = tr
        tape[h] = w
        h += d
        st = s
        n += 1
        lo, hi = min(lo, h), max(hi, h)
        if st == 1 and n > 5 and tape[h] == 1 and tape[h + 1] == 0 and not any(tape[h + 1:hi + 1]):
            # Z(t'): a run of 1s ending at the head, only 0s (blank as far as the machine knows) around it
            seg = bytes(tape[lo:h + 1]).lstrip(b"\x00")
            if all(seg):
                return len(seg)
    raise RuntimeError("no reset within %d steps" % maxs)


if __name__ == "__main__":
    bad = 0
    for t in range(2, int(sys.argv[1])):
        if next_z(t) != G(t):
            bad += 1
            print("mismatch", t, next_z(t), G(t))
    print("checked t < %s: %d mismatches" % (sys.argv[1], bad))
