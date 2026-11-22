"""check / run for the machines registered by clockx.py (same commands as clock.py)."""
import sys
import clockx  # noqa: F401  (registers)
from clockx import clock

_visits = clock.Hybrid.visits


def _visits_after_start(self, limit):
    """The visits of clock.Hybrid without the start (t = 0), where a machine started in its state X on the blank
    tape counts as visiting; tools/c/tmrun.c `at` prints only after a step."""
    for v in _visits(self, limit):
        if v[0] != 0:
            yield v


clock.Hybrid.visits = _visits_after_start
if __name__ == "__main__":
    m, cmd = sys.argv[1], sys.argv[2]
    if cmd == "check":
        print(clock.check(m, int(float(sys.argv[3]))))
    elif cmd == "tmcheck":
        print(clock.tmcheck(m, int(float(sys.argv[3])), *sys.argv[4:5]))
    else:
        clock.run(m, float(sys.argv[3]))
