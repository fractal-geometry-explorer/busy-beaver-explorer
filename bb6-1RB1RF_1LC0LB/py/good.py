"""The condition Good40600 of holdouts/1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---/lean/Lockstep.lean along the
accelerated run (`accel.py`), far past what the run-length simulators reach.

Good40600: in the run of 1RB1RF_1LC0LB_1RE0LD_1LB0RF_0RA0RC_1RE--- from blank tape the head never reads a 1 in state B
or C with only 0s to its right (`Bad`).  This program runs `accel.run` and checks Bad in each of its three kinds of
work:

* the macro steps of the concrete trips (`tools/py/bbtools/macro.py`, k = 4): every macro step whose block has blank
  tape beyond it on the right is replayed cell by cell, and each step of it checked;
* the cycle jumps inside concrete trips (`bbtools.cycles`): a jump repeats one proved cycle, so the head does in each
  copy what it did in the copy that ran (and was checked) before the jump, as long as the runs it meets keep their
  counts.  Near the right end that is checked: the counts of the last two runs that are not blank must not move;
* the bulk steps (counter trips in closed form): an argument, not a simulation.  A counter trip starts and ends at
  the right end `s_r (10)^W 0 10 0^inf` of its last level, and between the two it is left of the pairs (10)^W, which
  it crosses on the way out and on the way back (lean/Counter.lean: `counter_last2`, `counter_last1`,
  `counter_borrow*`).  So what it does right of them is one fixed sequence of steps for each of the three ways the
  trip can end (digit 2, 1 or 0 of the last level), the same for every W; and W only grows in counter trips.  Each
  of the three occurs among the concrete trips checked here and in every trip of the first 10^14 steps (checked
  cell by cell by holdouts/1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---/py/goodrun.py).  The smallest W a bulk step
  starts from is printed.

Trusted Python throughout, as accel.py is.

usage: python3 good.py STEPS          e.g. 1e30 (about an hour)
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "..", "..", "tools", "py"))
import accel  # noqa: E402
from bbtools import cycles  # noqa: E402
from bbtools.macro import MacroRun  # noqa: E402

B, C = 1, 2
BAD = []
CHECKED = [0]
JUMPS = {"jumps": 0, "right_end_moves": 0}


def _blank(st, zero):
    return len(st) <= 4 and all(x == zero for x, _ in st[1:])


_step = MacroRun.step


def step(self):
    """MacroRun.step, with the block replayed cell by cell first when blank tape lies beyond it on the right."""
    if not self.halted:
        q, d = self.state, self.dir
        zero = (0,) * self.k
        if d == 1:
            rest = [list(e) for e in self.right]
            if len(rest) > 1:
                rest[-1][1] -= 1
                if rest[-1][1] == 0:
                    rest.pop()
            x, beyond = self.right[-1][0], _blank(rest, zero)
        else:
            x, beyond = self.left[-1][0], _blank(self.right, zero)
        if beyond:
            CHECKED[0] += 1
            c, i = list(x), 0 if d == 1 else self.k - 1
            while 0 <= i < self.k:
                if q in (B, C) and c[i] == 1 and not any(c[i + 1:]):
                    BAD.append((self.steps, str(self)[:200]))
                    break
                t = self.m.table[q][c[i]]
                if t is None:
                    break
                c[i], mv, q = t
                i += mv
    return _step(self)


_apply = cycles.Rule.apply


def apply(self, run, k):
    """Rule.apply, after checking that the last two runs that are not blank keep their counts."""
    snap = cycles.snapshot(run)
    nl, nr = len(snap.left), len(snap.right)
    order = list(range(nl)) + [nl + j for j in reversed(range(nr))]
    words = [w for w, _ in snap.left] + [w for w, _ in snap.right]
    nonblank = [i for i in order if any(words[i])]
    JUMPS["jumps"] += 1
    if any(self.delta[i] for i in nonblank[-2:]):
        JUMPS["right_end_moves"] += 1
    return _apply(self, run, k)


def main(argv):
    if len(argv) != 1:
        sys.exit(__doc__)
    MacroRun.step = step
    cycles.Rule.apply = apply
    steps = int(float(argv[0]))
    nb = nc = 0
    minw = last = w = None
    for s, trips, t, kind in accel.run(steps):
        last = (s, trips)
        if kind == "bulk":
            nb += 1
            minw = w if minw is None else min(minw, w)
        else:
            nc += 1
        levs, _ = accel.regular(t)         # where the next step starts
        w = levs[0][2] if levs else None
        if BAD:
            print("Bad:", BAD[:3])
            return 1
        if (nb + nc) % 2000 == 0:
            print(f"{float(s):.3e} steps, {trips} trips, {nb} bulk steps, {nc} concrete trips", flush=True)
    print(f"{last[0]} steps ({float(last[0]):.3e}), {last[1]} trips: {nb} bulk steps, {nc} concrete trips; "
          f"{CHECKED[0]} blocks at the right end replayed; {JUMPS['jumps']} cycle jumps, "
          f"{JUMPS['right_end_moves']} moving a count near the right end; smallest last-level W a bulk step starts "
          f"from: {minw}; Bad: {len(BAD)}")
    return 1 if BAD or JUMPS["right_end_moves"] else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
