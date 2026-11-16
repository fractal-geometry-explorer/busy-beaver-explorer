"""The simulator of coq/M_1RB1RD_1RC1RB_1LD0RA_1RA0LE_1LF0LC_HHH1LE.v, in Python, with step counts.

It is py/leansim.py (the Lean simulator's algorithm) with three changes, the ones made for the Coq proof:

- no folding of cells into runs when they are pushed (runs come only from crossings, the canonical form and the
  macros);
- at every visit the left side is put in canonical form, whether or not a jump applies;
- two block rules for whole counter levels, tried before anything else:
    L: D moving left, front 1 0 (011)^k 1 ...  ->  front 1 ..., (100)^(k-1) 1 0 1 1 0 pushed behind  (5+3(k-1) steps)
    R: C moving right, front (100)^m 1 0 1 1 0 ...  ->  1 1 (011)^(m+1) pushed behind              (5+3m steps)

99% of the Lean simulator's 89M rounds are the overflow visits, where the head walks over all the levels of the
odometer and back; L and R take a level in one round. The run to the halt is 19.0M rounds (Coq needs fewer than
2^25) and gives the same step count as accel.py.

    python3 coqsim.py          about 60 s; prints the round counts and the halting step count
"""
import sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import leansim
from leansim import Sim, Halt, W
X = (1, 0, 0)
STEPS = 853177647932005270554892218084645935472995035642746848454477793277027802995098762076895667304703808111420498351739937140047615589683


class CoqSim(Sim):
    def __init__(s):
        super().__init__(); s.nL = s.nR = 0; s.ngen = 0; s.rounds = 0

    def pushBit(s, stk, b):
        stk.append(b)

    def macro(s):
        f = s.front
        if not s.dirR and s.st == 3:      # D, moving left (stacks: nearest cell last)
            if len(f) >= 4 and f[-1] == 1 and f[-2] == 0 and isinstance(f[-3], list) and f[-3][0] == W and f[-4] == 1:
                m = f[-3][1] - 1
                del f[-3:]
                for x in (0, 1, 1, 0, 1): s.back.append(x)
                if m > 0: s.back.append([X, m])
                s.steps += 5 + 3 * m; s.nL += 1; return True
            return False
        if s.dirR and s.st == 2:          # C, moving right
            i = len(f) - 1; m = 0
            if i >= 0 and isinstance(f[i], list):
                if f[i][0] != X: return False
                m = f[i][1]; i -= 1
            if i >= 4 and f[i] == 1 and f[i - 1] == 0 and f[i - 2] == 1 and f[i - 3] == 1 and f[i - 4] == 0:
                del f[i - 4:]
                s.back.append([W, m + 1]); s.back.append(1); s.back.append(1)
                s.steps += 5 + 3 * m; s.nR += 1; return True
        return False

    def run(s):
        try:
            while True:
                s.rounds += 1
                if s.dirR and not s.front and s.st == 0:
                    s.nvisit += 1
                    if not s.try_jump(): s.back = s.canon()
                if s.macro(): continue
                s.ngen += 1; s.step()
        except Halt:
            return True


if __name__ == '__main__':
    t = time.time(); s = CoqSim(); s.run()
    print('HALT at round', s.rounds, '(level macros: L', s.nL, 'R', s.nR, '; generic', s.ngen, '; visits', s.nvisit,
          '; jumps', s.njump, ')')
    print('steps', s.steps, 'agrees with accel.py' if s.steps == STEPS else 'DIFFERENT from accel.py')
    print('time %.0f s' % (time.time() - t))
