"""Doubling chains of 1RB1RF_1RC0RB_0RD1LF_1LE1RE_1LA---_1RA0LC, checked on the run.

Sample: the head in state A at the right end of the visited tape, on a 0.  The tape is then  P (10)^k 1^m  with the
head just right of the block of m ones, where P (the prefix) does not end in 10.  A chain starts with
P (10)^k 0 1^5 (the pairs are followed by one more 0); then the prefix stays P and (k, m) runs through
    (k, 11) -> (k-1, 18) -> (k-14, 48) -> (k-41, 110) -> (k-100, 232) -> (k-219, 478) -> ...
that is m_0 = 18, m_t = (92*2^t + (-1)^t)/3 - 13, and from m_t to m_(t+1) the pairs fall by
    d_t = (m_(t+1) - m_t)/2 - (2 if t is even else 4).
A chain ends when the pairs run out; what happens then depends on k, m and the prefix (not worked out yet).

usage (from the repository root):
    python3 holdouts/1RB1RF_1RC0RB_0RD1LF_1LE1RE_1LA---_1RA0LC/py/chains.py STEPS
runs tools/c/tmrun (compiled into /tmp) and checks every sample transition inside a chain against the rule above.
"""
import os, re, subprocess, sys, tempfile, collections

M = "1RB1RF_1RC0RB_0RD1LF_1LE1RE_1LA---_1RA0LC"
ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "..")


def mt(t):
    return (92 * 2 ** t + (-1) ** t) // 3 - 13


CHAIN = {mt(t): t for t in range(60)}


def samples(steps):
    exe = os.path.join(tempfile.gettempdir(), "bbx_tmrun")
    src = os.path.join(ROOT, "tools", "c", "tmrun.c")
    if not os.path.exists(exe) or os.path.getmtime(exe) < os.path.getmtime(src):
        subprocess.run(["cc", "-O2", "-o", exe, src], check=True)
    p = subprocess.Popen([exe, M, str(steps), "at", "A", "R", str(10 ** 9)], stdout=subprocess.PIPE, text=True)
    for line in p.stdout:
        t = line.split()
        if t[0] == "running" or t[0] == "halted" or not t[-1] == "A>0":
            continue
        cells = "".join(c.split("^")[0] * int(c.split("^")[1]) if "^" in c else c for c in t[1:-1])
        body = cells.rstrip("1")
        m = len(cells) - len(body)
        mm = re.search(r"((?:10)*)$", body)
        k = len(mm.group(1)) // 2
        yield int(t[0]), body[:len(body) - 2 * k], k, m


def main(steps):
    cnt = collections.Counter()
    bad = []
    prev = None
    for s in samples(steps):
        if prev is not None:
            _, p0, k0, m0 = prev
            _, p1, k1, m1 = s
            if m0 == 5:
                # at m = 5 the pairs sit before one more 0: P (10)^k 0 1^5 becomes P (10)^k 1^11
                ok = k0 == 0 and m1 == 11 and p0 == p1 + "10" * k1 + "0"
                cnt["5->11"] += 1
                if not ok: bad.append((prev, s))
            elif m0 == 11:
                ok = p1 == p0 and (k1, m1) == (k0 - 1, 18)
                cnt["11->18"] += 1
                if not ok: bad.append((prev, s))
            elif m0 in CHAIN and p1 == p0 and m1 == mt(CHAIN[m0] + 1):
                t = CHAIN[m0]
                d = (m1 - m0) // 2 - (2 if t % 2 == 0 else 4)
                cnt["chain"] += 1
                if k1 != k0 - d: bad.append((prev, s))
            else:
                cnt["other"] += 1
        prev = s
    print(dict(cnt), "mismatches:", len(bad))
    for b in bad[:5]:
        print("  ", b[0][0], b[0][2:], "->", b[1][0], b[1][2:])


if __name__ == "__main__":
    main(int(sys.argv[1]))
