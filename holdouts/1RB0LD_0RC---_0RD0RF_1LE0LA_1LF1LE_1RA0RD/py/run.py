"""The run of 1RB0LD_0RC---_0RD0RF_1LE0LA_1LF1LE_1RA0RD on the segment simulator with cycle jumps.

  python3 py/run.py check T     run past T steps, then compare the whole tape with the plain C simulator
                                (c/snap.c, compiled to /tmp) at the first sample point after T
  python3 py/run.py epochs SEC  print one line per epoch (the start of each phase B): steps, the 36-word counters
                                on the left, the 8-word count y; stop after SEC seconds of wall time

segsim.py keeps the tape as cells and repeats Rep(word, n) and crosses long repeats with shift rules it finds and
checks on one copy (two-sided carried words allowed); accel.py jumps k periods of a regime whose counts move by
constant amounts (checked over three periods).  Both are exact: `check` compares them with the plain simulator."""
import os, subprocess, sys, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from accel import Accel
from segsim import Rep, Halt

M = "1RB0LD_0RC---_0RD0RF_1LE0LA_1LF1LE_1RA0RD"
WORDS = "10011010,11111000,11110001,101010011010100110,100110101001101001".split(",")


def check(T):
    exe = "/tmp/snap_48815"
    subprocess.run(["gcc", "-O2", "-o", exe, os.path.join(HERE, "..", "c", "snap.c")], check=True)
    a = Accel(M, WORDS)
    def on(a):
        if a.s.steps > T:
            L, q, R = a.s.tape_str(); st = a.s.steps
            out = subprocess.run([exe, M, "100000000", str(st)], capture_output=True, text=True).stdout.split()
            tape = out[5]; i = tape.index(">")
            ok = tape[:i].lstrip("0") == L.lstrip("0") and tape[i+1:].rstrip("0") == R.rstrip("0") and out[4] == q
            print(f"steps {st}: tape {'equal' if ok else 'DIFFERENT'} ({a.jumps} jumps before)")
            raise SystemExit(0 if ok else 1)
    a.on_sample = on
    a.run(10**30)


def epochs(sec):
    a = Accel(M, WORDS); t0 = time.time()
    def log(a, p, d, k):
        if time.time() - t0 > sec: raise SystemExit
        if p in (1, 2):
            r36 = [t.n for t in a.s.left if isinstance(t, Rep) and len(t.w) == 36]
            y = [t.n for t in a.s.right if isinstance(t, Rep) and t.n > 10]
            print(f"{a.s.steps:.6e} counters {r36} y {y}", flush=True)
    try:
        a.run(10**400, log=log)
    except Halt:
        print("HALT at", a.s.steps)


if __name__ == "__main__":
    if sys.argv[1] == "check": check(float(sys.argv[2]))
    else: epochs(float(sys.argv[2]))
