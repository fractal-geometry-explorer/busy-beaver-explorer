"""The fast simulators of the two-stack form against twostack.zstep.

* py/accel.py without memo, step by step against zstep; with memo against without memo at every end turn
  (configuration, step count, counts, logged events);
* c/twostack.c `dump`, step by step against zstep;
* c/twostack.c `run` against the memoized py/accel.py at an end turn after 10^7 steps (row, counts);
* the near miss of the notes (a frame taken to 0 at step 204,719,421) with ACCEL_LONG=1.

usage: python3 tests/test_accel.py
"""
import os
import re
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, os.path.join(ROOT, "py"))

import accel  # noqa: E402
from callstack import start  # noqa: E402
from twostack import END, norm, zstep  # noqa: E402


def build():
    exe = os.path.join(tempfile.mkdtemp(), "twostack")
    subprocess.run(["gcc", "-O2", "-Wall", "-Werror", "-o", exe, os.path.join(ROOT, "c", "twostack.c")], check=True)
    return exe


def parse_row(lines):
    """L and R lines of twostack.c's dump -> a row of the two-stack form."""
    L = [int(x) for x in lines[0].split(":")[1].split()]
    row = [[x, 0] for x in L]
    frames = []
    for tok in lines[1].split(":")[1].split():
        v, g = re.match(r"(-?\d+)<(end|-?\d+)>", tok).groups()
        frames.append([int(v), END if g == "end" else int(g)])
    return norm(row + frames)


def test_accel(T=200000):
    fails, n, turns = accel.check(T)
    assert not fails, fails
    assert n >= T and turns > 50, (n, turns)
    print(f"accel: {n} steps equal to zstep, {turns} end turns memo = no memo")


def test_c_dump(exe, T=20000):
    out = subprocess.run([exe, "dump", str(T)], check=True, capture_output=True, text=True).stdout.splitlines()
    z = norm(start())
    k = 0
    for i in range(0, len(out), 3):
        assert out[i] == f"step {k + 1}", out[i]
        z = zstep(z)
        k += 1
        got = parse_row(out[i + 1:i + 3])
        assert got == z, (k, got[-6:], z[-6:])
    assert k == T
    print(f"twostack.c: {T} steps equal to zstep")


def test_c_run(exe, T=10 ** 7):
    t = accel.Top()
    while t.sim.steps < T:
        t.end_turn()
    S = t.sim.steps
    with tempfile.TemporaryDirectory() as d:
        st = os.path.join(d, "s.bin")
        out = subprocess.run([exe, "run", str(S), "-", st], check=True, capture_output=True, text=True).stdout
        final = [ln for ln in out.splitlines() if ln.startswith("final")][0]
        f = dict(re.findall(r"(\S+) (-?\d+)", final))
        c = t.sim.counts
        assert int(f["steps"]) == S
        assert (int(f["R2"]), int(f["to1"]), int(f["zero"])) == (c[accel.C_R2], c[accel.C_TO1], c[accel.C_ZERO]), (f, c)
        assert int(f["end"]) == t.endv
        lines = out.splitlines()
        assert parse_row(lines[-2:]) == norm(t.config()), (lines[-2:], t.config()[-6:])
        # resume: S more steps in one go, or in two pieces through the saved state, give the same state
        st2, st3 = os.path.join(d, "s2.bin"), os.path.join(d, "s3.bin")
        subprocess.run([exe, "run", str(2 * S), st, st2], check=True, capture_output=True)
        subprocess.run([exe, "run", str(2 * S), "-", st3], check=True, capture_output=True)
        assert open(st2, "rb").read() == open(st3, "rb").read()
    print(f"twostack.c run: row and counts equal to accel.py after {S} steps; resume from a saved state")


def test_near_miss(exe):
    out = subprocess.run([exe, "run", "3e8"], check=True, capture_output=True, text=True).stdout
    assert "near miss: step 204719421, a frame taken to 0 with gap 0" in out, out
    print("the near miss at step 204,719,421")


def main():
    exe = build()
    test_accel()
    test_c_dump(exe)
    test_c_run(exe)
    if os.environ.get("ACCEL_LONG"):
        test_near_miss(exe)
    print("ok")


if __name__ == "__main__":
    main()
