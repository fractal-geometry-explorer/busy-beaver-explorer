"""Macro simulator of 1RB0LD_1RC1RA_1LD0RB_1LE1LA_1RF0RC_---1RE with exact step counts (see lean/Macro.lean).

A phase start (a, K, j) is the tape 0^inf 1^a 0 0 (10)^K 1^(2j+1) C> 0^inf.  The step counts are those of the
theorems in lean/Rules.lean.  usage: python3 py/macro.py [check | epochs]"""
import sys

sys.set_int_max_str_digits(0)


def mstep(a, K, j):
    """(next phase start or None for a halt, steps taken; the halting transition counts)."""
    i = K // 2
    J = j + 3 * i
    s = 8 * i * j + 12 * i * (i - 1) + 14 * i
    if K % 2 == 0:
        if a == 0:
            return None, s + 8 * J + 13 + 1
        return (a - 1, J + 1, 0), s + 8 * J + 13
    if a == 0:
        return (2 * J + 7, 0, 1), s + 12 * J + 31 + 7
    return (a - 1, J + 3, 1), s + 12 * J + 33


def check(n=200):
    """Phase starts and step counts against the direct simulator, for the first n phases."""
    sys.path.insert(0, __file__.rsplit("/", 2)[0] + "/../../tools/py")
    from bbtools.machine import Machine, Run
    m = Machine.parse("1RB0LD_1RC1RA_1LD0RB_1LE1LA_1RF0RC_---1RE")
    r = Run(m)
    M, t = (3, 0, 1), 18
    r.run(18)
    for k in range(n):
        a, K, j = M
        cells = [1] * a + [0, 0] + [1, 0] * K + [1] * (2 * j + 1)
        # the tape left of the head, from the leftmost 1 (wall) to the head
        st, hd = r.state, r.head
        word = [r.tape.get(x) for x in range(hd - len(cells), hd)]
        assert st == 2 and word == cells and r.tape.get(hd) == 0, (k, M, t)
        assert all(r.tape.get(x) == 0 for x in range(hd - len(cells) - 6, hd - len(cells))), (k, M)
        M, s = mstep(*M)
        t += s
        r.run(t)
        assert r.steps == t
    print("checked", n, "phases,", t, "steps")


def digits(x):
    """Decimal digits of x (exact; the leading digits are found from the top 64 bits)."""
    from math import log10
    b = x.bit_length()
    if b <= 64:
        return len(str(x))
    sh = b - 64
    return int(log10(x >> sh) + sh * log10(2)) + 1


def epochs(count=3):
    A, t = 3, 18
    for e in range(count + 1):
        M = (A, 0, 1)
        for _ in range(A + 1):
            M, s = mstep(*M)
            t += s
            if M is None:
                print("halts at the end of epoch", e + 1, "after", t, "steps")
                return
        A = M[0]
        assert M[1:] == (0, 1)
        print(f"epoch {e + 1} survives; steps so far ~10^{digits(t) - 1}; "
              f"next wall has {digits(A)} digits" + (f" (= {A})" if A < 10 ** 9 else ""), flush=True)
        if e + 1 == count:
            return


if __name__ == "__main__":
    if sys.argv[1:2] == ["check"]:
        check(int(sys.argv[2]) if len(sys.argv) > 2 else 18)
    else:
        epochs()
