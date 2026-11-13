"""List the post-event configurations `P d bs` of a run from blank tape and check consecutive ones against the event
rule proved in `lean/Count.lean` (`event_rule`): P d (b1 :: lo ++ h) -> P (d+1) (b1 :: lo ++ inc h), |lo| = d,
when h has a 0.  Pairs where h has no 0 are overflows (not covered by the theorem) and are listed.

P d bs: state S on the first cell of the counter `(0 0 0)^d 0 0 1` (blank after it); left of the head
`1 1`, then the pairs `b 1` of bs top bit first, then `0 1`.

usage: python3 pchain.py MACHINE STATE STEPS      (S = B for 1RB---_1RC0RD_..., E for 1RB---_1LC1RE_...)
"""
import sys


def inc(l):
    l = l[:]
    for i, b in enumerate(l):
        if b == 0:
            l[i] = 1
            return l
        l[i] = 0
    return None


def pconfigs(m, S, nmax):
    tr = m.split("_")
    tape = bytearray(1 << 16)
    p = len(tape) // 2
    q, n = "A", 0
    lo = hi = p
    while n < nmax:
        x = tape[p]
        t = tr["ABCDEF".index(q)][3 * x:3 * x + 3]
        if t[2] == "-":
            yield ("HALT", n)
            return
        if q == S and x == 0:
            r = p + 1
            while r <= hi and tape[r] == 0:
                r += 1
            if r <= hi and (r - p) % 3 == 2 and all(tape[k] == 0 for k in range(r + 1, hi + 1)):
                l0 = lo
                while tape[l0] == 0:
                    l0 += 1
                s = bytes(tape[l0:p])
                if len(s) % 2 == 0 and s[:2] == b"\1\1" and s[-2:] == b"\0\1" and all(s[k] == 1 for k in range(3, len(s), 2)):
                    bits = [s[k] for k in range(2, len(s) - 2, 2)][::-1]
                    yield (n, (r - p - 2) // 3, bits)
        tape[p] = int(t[0])
        p += 1 if t[1] == "R" else -1
        q = t[2]
        n += 1
        lo, hi = min(lo, p), max(hi, p)


def main():
    m, S, nmax = sys.argv[1], sys.argv[2], int(float(sys.argv[3]))
    prev = None
    ok = ovf = bad = 0
    for row in pconfigs(m, S, nmax):
        if row[0] == "HALT":
            print("HALT at", row[1])
            break
        n, d, bs = row
        if prev:
            n0, d0, bs0 = prev
            h = bs0[d0 + 1:]
            if len(bs0) >= d0 + 1 and 0 in h:
                exp = bs0[:d0 + 1] + inc(h)
                if (d, bs) == (d0 + 1, exp):
                    ok += 1
                else:
                    bad += 1
                    print("MISMATCH", prev, row)
            else:
                ovf += 1
                print(f"overflow: step {n0} d={d0} bits(low first)={''.join(map(str, bs0))} -> step {n} d={d} {''.join(map(str, bs))}")
        prev = row
    print(f"{ok} phases follow event_rule, {ovf} overflows, {bad} mismatches")


if __name__ == "__main__":
    main()
