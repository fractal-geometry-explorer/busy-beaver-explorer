"""Cell-exact check of c/hsim2.cpp (accelerated, symbolically verified jumps) against plain simulation (c/dump.c).

usage (from the repo root):
  python3 holdouts/1RB0RE_0LC0RF_1LD1LC_1RA0LD_0RD1RE_---0LB/py/cmpc.py STEPS [K]
hsim2 runs until the first turn-around at or after STEPS; dump.c then runs exactly that many steps from blank tape and
the state and every written cell are compared.
"""
import os, subprocess, sys, tempfile

M = "1RB0RE_0LC0RF_1LD1LC_1RA0LD_0RD1RE_---0LB"
HERE = os.path.dirname(os.path.abspath(__file__))
C = os.path.join(HERE, "..", "c")


def build(tmp):
    subprocess.run(["g++", "-O2", "-o", os.path.join(tmp, "hsim2"), os.path.join(C, "hsim2.cpp")], check=True)
    subprocess.run(["gcc", "-O2", "-o", os.path.join(tmp, "dump"), os.path.join(C, "dump.c")], check=True)


def expand(part):
    return "".join(b * int(c) for b, c in (x.split(":") for x in part.split()))


def main():
    T = sys.argv[1]
    K = sys.argv[2] if len(sys.argv) > 2 else "30"
    with tempfile.TemporaryDirectory() as tmp:
        build(tmp)
        out = subprocess.run([os.path.join(tmp, "hsim2"), M, K, T, "100000", "1000000000000"],
                             capture_output=True, text=True, check=True).stdout.strip().split("\n")
        end = next(l for l in out if l.startswith("END"))
        tape = next(l for l in out if l.startswith("TAPE"))
        steps = int(end.split()[1])
        hd, lpart, rpart = tape.split("|")
        st = hd.split()[1]
        s = expand(lpart) + expand(rpart)
        d = subprocess.run([os.path.join(tmp, "dump"), M, str(steps)], capture_output=True, text=True,
                           check=True).stdout.split("\n")
    print(end)
    same = s.strip("0") == d[1].strip("0") and d[0].split()[0] == st
    print(f"steps {steps}: state {st} (direct {d[0].split()[0]}), {len(d[1])} cells, {'EQUAL' if same else 'DIFFERENT'}")
    sys.exit(0 if same else 1)


if __name__ == "__main__":
    main()
