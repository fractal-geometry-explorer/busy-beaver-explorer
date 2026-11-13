"""Check the round laws of 1RB1RA_1RC1LB_0LD0RA_1RF1LE_---1LF_1LC0LF against direct simulation (../c/blk.c).

A *block configuration* [b1, ..., bk] is the tape 0^inf 1^b1 0 1^b2 0 ... 0 1^bk C>0 0^inf.  A *round* runs from one
block configuration to the next one the machine reaches (the head in C on the first 0 right of all the 1s, the tape
a pure block word).  Laws checked here, for every listed context in front of A:

  odd   [.., A, n] -> [.., A, n + 2]        n odd, 3 <= n <= 2A + 1, in 3 * 2^((n+3)/2) - 6 steps
  even  [.., A, n] -> [.., A - 1, n - 1, 3]  n even, 4 <= n <= 2A + 2, in 6 * 2^(n/2) - 2n - 2 steps
        [.., A, 2] -> [.., A - 1, 5]

usage: python3 verify_rounds.py [AMAX]      (builds ../c/blk.c into the temp directory, or set BLK)
"""
import os, subprocess, sys, tempfile

M = "1RB1RA_1RC1LB_0LD0RA_1RF1LE_---1LF_1LC0LF"
HERE = os.path.dirname(os.path.abspath(__file__))
BLK = os.environ.get("BLK") or os.path.join(tempfile.gettempdir(), "blk_1RB1RA_1RC1LB")


def build():
    if not os.path.exists(BLK):
        subprocess.run(["gcc", "-O2", "-o", BLK, os.path.join(HERE, "..", "c", "blk.c")], check=True)


def round_(blocks, maxsteps=10**11):
    out = subprocess.run([BLK, M, "C", str(maxsteps), ",".join(map(str, blocks))], capture_output=True,
                         text=True, check=True).stdout.split()
    if out[0] == "ok":
        return int(out[1]), [int(x) for x in out[2].strip("[]").split(",")]
    return out[0], None


def main(amax):
    build()
    contexts = [[], [2], [7], [5, 3], [1, 9, 4]]
    n_checked = 0
    for A in range(1, amax + 1):
        for ctx in contexts:
            for n in range(2, 2 * A + 3):
                steps, res = round_(ctx + [A, n])
                if n % 2:
                    if n == 1:
                        continue
                    want = ctx + [A, n + 2]
                    assert res == want and steps == 3 * 2 ** ((n + 3) // 2) - 6, (ctx, A, n, steps, res)
                else:
                    want = ctx + [A - 1, 5] if n == 2 else ctx + [A - 1, n - 1, 3]
                    if A == 1:
                        continue        # A - 1 = 0: the blocks merge, not part of the law
                    assert res == want, (ctx, A, n, steps, res)
                    assert n == 2 or steps == 6 * 2 ** (n // 2) - 2 * n - 2, (ctx, A, n, steps)
                n_checked += 1
    print(f"ok: {n_checked} rounds, A <= {amax}, contexts {contexts}")


if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 12)
