"""py/largeblocks.py: the large-block counts along the orbit and the sentinel orbit, and the lists of
lean/Large.lean.  python3 tests/test_largeblocks.py"""
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "py"))
import largeblocks as lb  # noqa: E402
from invsearch import psi  # noqa: E402


def test_shift():
    assert psi(lb.V) == 0 and lb.V[0] == 0
    assert lb.WL == [31, 254304, 870464, 844832, 256088, 32930, 8427]
    assert lb.WLB == [255, 255488, 872704, 847232, 261464, 43362, 14699]


def test_witnesses():
    for y, firsts in ((lb.WL, [31, 15, 15, 7, 7, 3, 3, 1, 1]),
                      (lb.WLB, [255, 127, 127, 63, 63, 31, 31, 15, 15, 7, 7, 3, 3, 3, 3, 1, 1, 1, 1])):
        assert psi(y) == -57 and sum(y) % 4 == 0 and all(b >= 2 for b in y[1:])
        rows, end = lb.profile(y)
        assert end is None                                  # a stop at a block of 1
        assert [r[0] for r in rows] == firsts
        assert max(r[3] for r in rows) == 5 and max(r[2] for r in rows) == 5
    # the same rows as lean/Large.lean (`wL_large`)
    rows, _ = lb.profile(lb.WL)
    assert rows == [(31, 7, 4, 4), (15, 8, 4, 5), (15, 7, 4, 5), (7, 8, 4, 5), (7, 7, 4, 5), (3, 8, 5, 5),
                    (3, 7, 4, 4), (1, 8, 4, 5), (1, 7, 3, 4)]


def test_any_scale():
    # the shift 2^M * V works for every M from 6 (W7) and from 12 (WLB's base), with at most 5 large blocks
    for base, m0 in ((lb.W7, 6), (lb.W7B, 12)):
        for m in range(m0, 41):
            rows, end = lb.profile([a + 2 ** m * b for a, b in zip(base, lb.V)], 200)
            assert end is None and rows[-1][0] == 1 and max(r[3] for r in rows) <= 5, (m, rows)


def test_orbit():
    best = lb.most_large(lb.orbit_lists(300000))
    assert best[5][0] == 5 and best[5][1] == 269207, best
    assert best[1][0] == 1


def test_loose():
    best = lb.most_large(lb.loose_lists(300000), skip=20)
    assert best[5][0] == 5 and best[5][1] == 269209, best


if __name__ == "__main__":
    for name, f in list(globals().items()):
        if name.startswith("test_"):
            f()
            print(name, "ok")
