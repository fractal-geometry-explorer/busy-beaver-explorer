"""Levels of the separator counter of 1RB0RA_1LC0RC_1LF0RD_1RA1LE_0LC---_1LD0LA (trusted computation, observations).

usage: ./leftsnaps 3000000000 | python3 py/levels.py

Reads the sweep snapshots of c/leftsnaps.c (the tape each time the head extends it on the left in state D) and
writes each tape as  n0 S1 n1 S2 n2 ...: blocks (011)^n (the number n) and the separators between them (`1`, `01`,
`111`; a few other words near the right end).  Level j is the triple (S_{2j-1}, n_{2j-1}, S_{2j}).  For each level
it finds the smallest period p (tried: 8, 16, ..., 4096) and the first sweep from which the sequence of that level is
exactly periodic up to the last snapshot, and it prints the sweeps (mod 64) at which the tape beyond level 3 changes, and the last tape's first tokens.
"""
import re
import sys

PAT = re.compile(r"(011)+")


def tokens(t):
    out, pos = [], 0
    for m in PAT.finditer(t):
        if m.start() > pos:
            out.append(t[pos:m.start()])
        out.append((m.end() - m.start()) // 3)
        pos = m.end()
    if pos < len(t):
        out.append(t[pos:])
    return out


def main():
    snaps = []
    for line in sys.stdin:
        parts = line.split()
        if len(parts) == 3 and parts[1] == "D":
            snaps.append((int(parts[0]), tokens(parts[2])))
    print(f"{len(snaps)} sweeps, last at step {snaps[-1][0]}")
    g = lambda o, k: o[k] if len(o) > k else None
    for lev in range(1, 7):
        ks = (4 * lev - 3, 4 * lev - 2, 4 * lev - 1)
        seq = [tuple(g(o, k) for k in ks) for _, o in snaps]
        found = None
        per = 8
        while per <= 4096 and not found:
            for k in range(0, len(seq) - 3 * per, max(1, per // 4)):
                if all(seq[k + j] == seq[k + j + per] for j in range(len(seq) - k - per)):
                    found = (per, k)
                    break
            per *= 2
        if found:
            print(f"level {lev}: period {found[0]} sweeps from sweep {found[1]} (step {snaps[found[1]][0]})")
        else:
            print(f"level {lev}: no period up to 4096")
    ch, prev = [], None
    for k, (_, o) in enumerate(snaps):
        if tuple(o[12:]) != prev:
            ch.append(k)
            prev = tuple(o[12:])
    late = [k for k in ch if k >= 1000]
    phases = sorted({k % 64 for k in late})
    print(f"the tape beyond level 3 changes at {len(late)} sweeps from sweep 1000 on, at sweep numbers "
          f"= {phases} mod 64 only" if all(k % 64 in phases for k in late) else "")
    print("last tape:", " ".join(map(str, snaps[-1][1][:40])))


if __name__ == "__main__":
    main()
