"""py/bigfront.py: the runs of the orbit, the exact search, and the lists of lean/BigFront.lean.
python3 tests/test_bigfront.py"""
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "py"))
import bigfront as bf  # noqa: E402
from invsearch import psi  # noqa: E402


def test_witnesses():
    for y, p, n, frac in ((bf.WF, -23, 19, 4), (bf.WH, 1, 21, 5)):
        assert psi(y) == p and sum(y) % 4 == 0 and all(b >= 2 for b in y[1:])
        assert y[0] == 255 and sum(y) <= frac * y[0]
        rows, end = bf.trace(y)
        assert end == "stop at a block of 1" and len(rows) == n
        firsts = [r[0] for r in rows]
        assert all(b in (a, (a - 1) // 2) for a, b in zip(firsts, firsts[1:])) and firsts[-1] == 1
    # the rows of lean/BigFront.lean (`wF_firsts`)
    rows, _ = bf.trace(bf.WF)
    assert [(r[0], r[1]) for r in rows] == [
        (255, 7), (127, 8), (127, 7), (127, 6), (63, 7), (63, 6), (63, 5), (31, 6), (31, 5), (15, 6), (15, 5),
        (7, 6), (7, 5), (3, 6), (3, 5), (1, 6), (1, 5), (1, 4), (1, 3)]


def test_search():
    # the smallest 7-block lists, |psi| <= 21, first block 31: ones 112
    r, _ = bf.search(7, 4, 5 * 31 + 1, W=21)
    assert r is not None and r[0] == 112
    y = r[1]
    assert y[0] == 31 and sum(y) == 112 and abs(psi(y)) <= 21 and sum(y) % 4 == 0
    assert bf.trace(y)[1] == "stop at a block of 1"
    # every list the search returns is checked on the closed form
    for k0, H in ((6, 3), (7, 3), (8, 4)):
        r, _ = bf.search(k0, H, 16 * (2 ** (H + 1) - 1), W=60)
        assert r is not None and bf.trace(r[1])[1] == "stop at a block of 1"
        assert sum(r[1]) <= 4 * r[1][0]          # the first block is at least a quarter of the ones
    # no 7-block list with first block 3 or 7 and ones <= 5 f (the other blocks alone are at least 12)
    assert bf.search(7, 1, 5 * 3 + 1, W=21)[0] is None


def test_orbit():
    hist, low, most, slack = bf.orbit_summary(300000)
    assert most[0] == 2 and low[0] > 0.16 and slack[0] > 4.9
    assert sum(hist.values()) > 180000
    assert all(row[4] <= 2 for row in bf.orbit_runs(2000))


if __name__ == "__main__":
    test_witnesses()
    test_search()
    test_orbit()
    print("bigfront: all tests pass")
