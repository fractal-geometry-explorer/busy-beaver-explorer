"""Can a run of full passes from a loop entry of the clean-tape tree end at a right end in [RLO, RHI]?
(Untrusted; `../lean/END_TO_END.md`, "The chain ends at a right end of at least 769".)

Each entry class is a line z -> (b, W, R) (affine, integer z >= lo, from `../lean/EntryForms.lean`), with left
countdown L1 = 147b - 112W + 392R - 186.  p full passes from the entry end at right end r when R(z) = 16^p r and
L1(z) = 64^p l (l = 3 mod 7 holds at every pass start, since 64 = 1 mod 7); after a half pass, when W = 2 (mod 4) is
possible on the class, the same with R/2 and (L1 + 35W - 147R - 60)/2.  This is the arithmetic of `NoEndBelow`
(`../lean/BB6/BigEnd.lean`), which Lean checks for r < 769 (`bigEntryOK`).  For each p, R(z) = 16^p r fixes z; p
stops once |L1| < 3 * 64^p on the whole stretch of the line where r <= RHI, since then no l is left.

usage: python3 chain_end.py entries36.txt 178 5000   (entries36.txt from `../lean/EntryForms.lean 2199023255552 36`)
"""
import sys

G = 2 ** 41  # the cone: entries of width at least 2^41


def ends(R0, R1, L0, L1, lo, rlo, rhi, den=1):
    """The (p, r, z, l) with (R0 + R1 z)/den = 16^p r, (L0 + L1 z)/den = 64^p l, z >= lo integer, rlo <= r <= rhi."""
    out = []
    for p in range(64):
        X, Y = 16 ** p, 64 ** p
        if R0 + R1 * lo > den * X * rhi:  # R grows along the line (R1 > 0): every r is below the cone's edge
            continue
        for r in range(rlo, rhi + 1):
            num = den * X * r - R0
            if num % R1:
                continue
            z = num // R1
            if z < lo:
                continue
            Lz = L0 + L1 * z
            if Lz % den or (Lz // den) % Y:
                continue
            out.append((p, r, z, Lz // den // Y))
        zmax = (den * X * rhi - R0) // R1
        if zmax >= lo and max(abs(L0 + L1 * lo), abs(L0 + L1 * zmax)) // den < 3 * Y:
            break
    return out


def main():
    fn, rlo, rhi = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    n = nh = 0
    hits = []
    for line in open(fn):
        if not line.startswith('E '):
            continue
        parts = line[2:].split('|')
        a, b, c, W = [list(map(int, p.split()))[:2] for p in parts[1:5]]
        ts = [list(map(int, t.split()))[:2] for t in parts[5].split(';')]
        lo = max(-((t[0] - G) // t[1]) for t in ts)
        R0, R1 = W[0] - c[0] - 1, W[1] - c[1]
        L0 = 147 * b[0] - 112 * W[0] + 392 * R0 - 186
        L1 = 147 * b[1] - 112 * W[1] + 392 * R1
        assert R1 > 0
        n += 1
        hits += [('full', n, h) for h in ends(R0, R1, L0, L1, lo, rlo, rhi)]
        if W[1] % 4 or W[0] % 4 == 2:  # W = 2 (mod 4) somewhere on the line: a half pass can start the chain
            nh += 1
            HL0 = L0 + 35 * W[0] - 147 * R0 - 60
            HL1 = L1 + 35 * W[1] - 147 * R1
            hits += [('half', n, h) for h in ends(R0, R1, HL0, HL1, lo, rlo, rhi, den=2)
                     if (W[0] + W[1] * h[2]) % 4 == 2]
    print('entry classes', n, 'with a possible half pass', nh, 'ends at r in [%d, %d]:' % (rlo, rhi), len(hits))
    for h in hits:
        print(*h)


if __name__ == '__main__':
    main()
