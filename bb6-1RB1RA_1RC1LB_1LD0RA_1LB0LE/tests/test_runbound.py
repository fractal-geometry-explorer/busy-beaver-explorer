"""py/runbound.py: the run bound by block count, the cycles from 7 blocks on, the witness of lean/Run7.lean, and
the rule of `front_second`.  python3 tests/test_runbound.py"""
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "py"))
import passmap  # noqa: E402
import runbound  # noqa: E402
from invsearch import psi  # noqa: E402


def test_table():
    t = runbound.table(300)
    assert [t[k][1] for k in range(2, 7)] == [1, 4, 6, 10, 17], t


def test_cycles():
    parts = runbound.cyclic_parts(100)
    ks = sorted(tuple(sorted({s[0] for s in p})) for p in parts)
    assert (7, 8) in ks, ks
    assert all(min(k) >= 7 for k in ks), ks
    # every cycle has front stops
    assert all(any(s[2] for s in p) for p in parts)


def test_witness():
    y = runbound.W7
    assert psi(y) == -57 and sum(y) % 4 == 0 and y[0] == 2 ** 5 - 1 and y[1] >= y[0] + 2
    assert all(b >= 2 for b in y[1:])
    out, end = runbound.trace(y)
    assert end == "stop at a block of 1"
    assert [r[0] for r in out] == [31, 15, 15, 7, 7, 3, 3, 1, 1]
    assert [r[1] for r in out] == [7, 8] * 4 + [7]
    # the same lists as Lean's run (nearest first there)
    z = y
    for _ in range(8):
        z = passmap.passmap(z)
    assert z == [1, 14, 40, 194, 362, 114, 15]


def test_second():
    runbound.check_second(3000)


if __name__ == "__main__":
    for name, f in list(globals().items()):
        if name.startswith("test_"):
            f()
            print(name, "ok")
