"""Epochs of 1RB0LA_1RC0RE_0LD0RF_1LA1LD_0RA1RE_---0LC: left-A records of the form E(n, S) = A> (01111)^n S, S short.

usage: python3 epochs.py run STEPS            the epoch records along the run from blank tape
       python3 epochs.py map TAIL N0 N1        for n in [N0, N1): from A> (01111)^n TAIL (blank elsewhere), the next
                                               epoch record (n' > n + 10): n', n' - 8n, its tail
       python3 epochs.py table N0              `map` for the six tails S0..S5 and n in [N0, N0+8)

Runs use c/epochs.c (compiled on first use into /tmp).
"""
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
M = "1RB0LA_1RC0RE_0LD0RF_1LA1LD_0RA1RE_---0LC"
EXE = "/tmp/epochs_M2"
TAILS = {"S0": "0011110111110111", "S1": "00111101111001", "S2": "0011110111101111001111000111",
         "S3": "001111011110111", "S4": "0011110111100111", "S5": "00111101111001100111"}
NAME = {v: k for k, v in TAILS.items()}


def exe():
    if not os.path.exists(EXE):
        subprocess.run(["gcc", "-O2", "-o", EXE, os.path.join(HERE, "..", "c", "epochs.c")], check=True)
    return EXE


def records(steps, tape=None):
    args = [exe(), M, str(steps)] + ([tape] if tape else [])
    p = subprocess.Popen(args, stdout=subprocess.PIPE, text=True)
    try:
        for line in p.stdout:
            f = line.split()
            if f[0] in ("HALT", "END", "OUT"):
                yield (f[0],)
                return
            yield int(f[0]), int(f[1]), f[2] if len(f) > 2 else ""
    finally:
        p.kill()


def next_epoch(n, tail, steps=10 ** 11):
    for r in records(steps, "01111" * n + tail):
        if len(r) == 1:
            return r
        if r[1] > n + 10:
            return r


def main():
    cmd = sys.argv[1]
    if cmd == "run":
        for r in records(int(float(sys.argv[2]))):
            print(*r if len(r) == 1 else (f"{r[0]:>14,}", r[1], NAME.get(r[2], r[2])))
    elif cmd in ("map", "table"):
        tails = [sys.argv[2]] if cmd == "map" else list(TAILS)
        n0 = int(sys.argv[3] if cmd == "map" else sys.argv[2])
        n1 = int(sys.argv[4]) if cmd == "map" else n0 + 8
        for t in tails:
            for n in range(n0, n1):
                r = next_epoch(n, TAILS.get(t, t))
                if len(r) == 1:
                    print(t, n, r[0])
                else:
                    print(t, n, "n mod 4 =", n % 4, "->", NAME.get(r[2], r[2]), r[1], "= 8n%+d" % (r[1] - 8 * n),
                          "steps", r[0], flush=True)


if __name__ == "__main__":
    main()
