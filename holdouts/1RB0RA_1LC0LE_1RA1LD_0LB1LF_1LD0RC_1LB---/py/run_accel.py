"""Run the machine with the shared cycle accelerator (bbtools.cycles over bbtools.macro, blocks of 3 cells) up to
10^E steps and print, at each power of ten, how many cycle rules have been proved and how many jumps made.

    python3 run_accel.py 1000        # about 7 minutes; no halt in the first 10^1000 steps

Each jump applies a cycle rule that bbtools.symtm proves symbolically (for all values of its variables); the run is
exact (tools/tests/test_tools.py checks the accelerator against plain macro runs)."""
import os, sys, time
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "../../../tools/py"))
from bbtools.cycles import Accelerator, snapshot
from bbtools.macro import MacroRun

M = "1RB0RA_1LC0LE_1RA1LD_0LB1LF_1LD0RC_1LB---"


def main(E):
    N = 10 ** E
    a = Accelerator(MacroRun(M, 3))
    r = a.run_
    t0, e = time.time(), 1
    while r.steps < N and not r.halted:
        if not r.step():
            break
        if a.sample(r):
            s = snapshot(r)
            h = a.hist.pop(s.key(), [])
            a.hist[s.key()] = h
            h.append(s)
            del h[:-3]
            a.jump(limit=N)
        while e <= E and r.steps > 10 ** e:
            print(f"10^{e}: {len(a.rules)} rules, {len(a.jumps)} jumps, {time.time() - t0:.1f} s", flush=True)
            e += 1
    print("HALTED" if r.halted else "no halt", "at", r.steps)
    print(str(r)[:3000])


if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 100)
