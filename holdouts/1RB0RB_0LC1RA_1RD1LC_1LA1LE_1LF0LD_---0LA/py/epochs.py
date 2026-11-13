"""Epoch experiments for 1RB0RB_0LC1RA_1RD1LC_1LA1LE_1LF0LD_---0LA with the macro simulator c/mrun.c.

An epoch ends when the head first visits a new cell on the far left (mode 2 of mrun prints the tape there).
  python3 py/epochs.py epoch3 M1,M2,...      third-epoch length for start tape P (01)^M (the real run has M = 520)
  python3 py/epochs.py epoch4 M1,... N1,...  end of epoch 3 from P (01)^M, then the next epoch with the
                                             trailing (10)^N replaced by (10)^N2 for each N2: H = halts
The numbers are those of a simulator (trusted, not proved)."""
import os, re, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
M = "1RB0RB_0LC1RA_1RD1LC_1LA1LE_1LF0LD_---0LA"
P = "1111010101110101011101010111010101110101011101010101110101011101011101010111010101110101110101011101010111"
EXE = os.path.join(tempfile.gettempdir(), "mrun_77294")
if not os.path.exists(EXE):
    subprocess.run(["gcc", "-O2", "-o", EXE, os.path.join(HERE, "../c/mrun.c")], check=True)


def rle(x):
    return " ".join(f"{g[0]}^{len(g)}" if len(g) > 1 else g for g in (m.group(0) for m in re.finditer(r"0+|1+", x)))


def leftrec(args):
    """run mrun (K=2, mode 2) and parse its LEFTREC line; None if it halted or found none."""
    out = subprocess.run([EXE, M, "2", "1e18", "2"] + args, capture_output=True, text=True).stdout.split()
    if not out or out[0] != "LEFTREC":
        return None, " ".join(out)
    return dict(steps=float(out[2]), exc=int(out[4]), state=out[6], dir=out[8], tape=out[10].replace("|", "")), None


def split_tail(tape):
    """an epoch end: core (10)^n tail, tail the last 3 cells."""
    core, n = tape[:-3], 0
    while core.endswith("10"):
        core, n = core[:-2], n + 1
    return core, n, tape[-3:]


def end3(m):
    r, err = leftrec([P + "01" * m, "A"])
    return r


if __name__ == "__main__":
    what = sys.argv[1]
    ms = [int(x) for x in sys.argv[2].split(",")]
    if what == "epoch3":
        for m in ms:
            r = end3(m)
            core, n, tl = split_tail(r["tape"])
            print(m, "excursions", r["exc"], "steps %.6e" % r["steps"], "end state", r["state"], "trailing (10)^N, N =", n,
                  "core", len(core), "cells", flush=True)
    elif what == "epoch4":
        Ns = [int(x) for x in sys.argv[3].split(",")]
        for m in ms:
            r = end3(m)
            core, n, tl = split_tail(r["tape"])
            row = []
            for N2 in Ns:
                r2, err = leftrec([core + "10" * N2 + tl, r["state"], r["dir"]])
                row.append("H" if r2 is None and err.startswith("HALT") else (f"{r2['exc']}" if r2 else "?"))
            print(m, "t=%d" % ((m - 4) // 12), "E3", r["exc"], "N", n, "N%12", n % 12,
                  " ".join(f"{a}:{b}" for a, b in zip(Ns, row)), flush=True)
    elif what == "law":
        # check E(m+12) = 4 E(m) + 2 for the listed m
        for m in ms:
            a, b = end3(m)["exc"], end3(m + 12)["exc"]
            print(m, a, b, "ok" if b == 4 * a + 2 else "FAILS", flush=True)
