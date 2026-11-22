"""The list machine of lean/End.lean run from this machine's first right turn (lean/Start.lean).

The list machine and its helpers are those of 1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF (py/listmachine.py and
py/race.py there), written in that machine's state names.  This machine is that table started in state E, so:

  python3 listrun.py lockstep N   compare the list machine with every right turn of the first N steps of this
                                  machine (run as that table from state E; a right turn is state A here, E there)
  python3 listrun.py run K        K list steps from START, checking that it never fails and far parts stay clean
  python3 listrun.py race K       witnesses at crossing turns with blank end (Race.lean), as race.py there
"""
import inspect
import os
import sys

OTHER = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..",
                     "1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF", "py")
sys.path.insert(0, OTHER)
import listmachine as lm  # noqa: E402
import race as rc  # noqa: E402

START_PY = "('EO', (Tr, F, Tr, F, F, F), ('pre', 1))"      # step 48: EO [b, a, b, a, a, a], prefix 1


def retarget(fn, old, new, mod):
    src = inspect.getsource(fn)
    assert old in src, (fn.__name__, old)
    ns = dict(vars(mod))
    exec(src.replace(old, new), ns)
    return ns[fn.__name__]


if __name__ == "__main__":
    mode, n = sys.argv[1], int(float(sys.argv[2]))
    if mode == "lockstep":
        retarget(lm.lockstep, "={},0,'A',0,0,0", "={},0,'E',0,0,0", lm)(n)
    elif mode == "run":
        retarget(lm.run, "('EO', (Tr, F), ('pre', 1))", START_PY, lm)(n)
    elif mode == "race":
        retarget(rc.race, "('EO', (True, False), ('pre', 1))",
                 START_PY.replace("Tr", "True").replace("F", "False"), rc)(n)
    else:
        sys.exit(__doc__)
